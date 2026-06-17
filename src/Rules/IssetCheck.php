<?php declare(strict_types = 1);

namespace PHPStan\Rules;

use PhpParser\Node;
use PhpParser\Node\Expr;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\IssetabilityDescriptor;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\Scope;
use PHPStan\DependencyInjection\AutowiredParameter;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Expr\PropertyInitializationExpr;
use PHPStan\Rules\Properties\PropertyDescriptor;
use PHPStan\ShouldNotHappenException;
use PHPStan\Type\NeverType;
use PHPStan\Type\Type;
use PHPStan\Type\VerbosityLevel;
use function sprintf;
use function str_starts_with;

/**
 * @phpstan-type ErrorIdentifier = 'empty'|'isset'|'nullCoalesce'
 */
#[AutowiredService]
final class IssetCheck
{

	public function __construct(
		private PropertyDescriptor $propertyDescriptor,
		#[AutowiredParameter]
		private bool $checkAdvancedIsset,
		#[AutowiredParameter]
		private bool $treatPhpDocTypesAsCertain,
	)
	{
	}

	/**
	 * @param ErrorIdentifier $identifier
	 * @param callable(Type): ?string $typeMessageCallback
	 */
	public function check(Expr $expr, Scope $scope, string $operatorDescription, string $identifier, callable $typeMessageCallback, ?IdentifierRuleError $error = null): ?IdentifierRuleError
	{
		$mutatingScope = $scope->toMutatingScope();

		return $this->doCheck($mutatingScope->getIssetabilityDescriptor($expr), $expr, $scope, $mutatingScope, $operatorDescription, $identifier, $typeMessageCallback, $error);
	}

	/**
	 * @param ErrorIdentifier $identifier
	 * @param callable(Type): ?string $typeMessageCallback
	 */
	private function doCheck(?IssetabilityDescriptor $descriptor, Expr $expr, Scope $scope, MutatingScope $mutatingScope, string $operatorDescription, string $identifier, callable $typeMessageCallback, ?IdentifierRuleError $error): ?IdentifierRuleError
	{
		// folds PHPStan\Analyser\IssetabilityDescriptor; mirrors PHPStan\Analyser\MutatingScope::issetCheck()
		if ($descriptor !== null && $descriptor->isVariable()) {
			$variableName = $descriptor->getVariableName();
			if ($variableName === null) {
				throw new ShouldNotHappenException();
			}

			$hasVariable = $scope->hasVariableType($variableName);
			if ($hasVariable->maybe()) {
				return null;
			}

			if ($error === null) {
				if ($hasVariable->yes()) {
					if ($variableName === '_SESSION') {
						return null;
					}

					$type = $this->treatPhpDocTypesAsCertain ? $scope->getScopeType($expr) : $scope->getScopeNativeType($expr);
					if (!$type instanceof NeverType) {
						return $this->generateError(
							$type,
							sprintf('Variable $%s %s always exists and', $variableName, $operatorDescription),
							$typeMessageCallback,
							$identifier,
							'variable',
						);
					}
				}

				return RuleErrorBuilder::message(sprintf('Variable $%s %s is never defined.', $variableName, $operatorDescription))
					->identifier(sprintf('%s.variable', $identifier))
					->build();
			}

			return $error;
		} elseif ($descriptor !== null && $descriptor->isOffset()) {
			$varResult = $descriptor->getVarResult();
			$dimResult = $descriptor->getDimResult();
			if ($varResult === null || $dimResult === null) {
				throw new ShouldNotHappenException();
			}

			$type = $this->treatPhpDocTypesAsCertain
				? $varResult->getTypeForScope($mutatingScope)
				: $varResult->getNativeTypeForScope($mutatingScope);
			if (!$type->isOffsetAccessible()->yes()) {
				return $error ?? $this->checkUndefinedInner($varResult, $scope, $mutatingScope, $operatorDescription, $identifier);
			}

			$dimType = $this->treatPhpDocTypesAsCertain
				? $dimResult->getTypeForScope($mutatingScope)
				: $dimResult->getNativeTypeForScope($mutatingScope);
			$hasOffsetValue = $type->hasOffsetValueType($dimType);
			if ($hasOffsetValue->no()) {
				if (!$this->checkAdvancedIsset) {
					return null;
				}

				return RuleErrorBuilder::message(
					sprintf(
						'Offset %s on %s %s does not exist.',
						$dimType->describe(VerbosityLevel::value()),
						$type->describe(VerbosityLevel::value()),
						$operatorDescription,
					),
				)->identifier(sprintf('%s.offset', $identifier))->build();
			}

			// If offset cannot be null, store this error message and see if one of the earlier offsets is.
			// E.g. $array['a']['b']['c'] ?? null; is a valid coalesce if a OR b or C might be null.
			if ($hasOffsetValue->yes() || $scope->hasExpressionType($expr)->yes()) {
				if (!$this->checkAdvancedIsset) {
					return null;
				}

				$error ??= $this->generateError($type->getOffsetValueType($dimType), sprintf(
					'Offset %s on %s %s always exists and',
					$dimType->describe(VerbosityLevel::value()),
					$type->describe(VerbosityLevel::value()),
					$operatorDescription,
				), $typeMessageCallback, $identifier, 'offset');

				if ($error !== null) {
					return $this->doCheck($varResult->getIssetabilityDescriptor(), $varResult->getExpr(), $scope, $mutatingScope, $operatorDescription, $identifier, $typeMessageCallback, $error);
				}
			}

			// Has offset, it is nullable
			return null;

		} elseif ($descriptor !== null && $descriptor->isProperty()) {

			$propertyFetch = $descriptor->getPropertyFetch();
			if ($propertyFetch === null) {
				throw new ShouldNotHappenException();
			}
			$innerResult = $descriptor->getInnerResult();

			$propertyReflection = $descriptor->resolvePropertyReflection($mutatingScope);

			if ($propertyReflection === null) {
				return $innerResult !== null
					? $this->checkUndefinedInner($innerResult, $scope, $mutatingScope, $operatorDescription, $identifier)
					: null;
			}

			if (!$propertyReflection->isNative()) {
				return $innerResult !== null
					? $this->checkUndefinedInner($innerResult, $scope, $mutatingScope, $operatorDescription, $identifier)
					: null;
			}

			if ($propertyReflection->hasNativeType() && !$propertyReflection->isVirtual()->yes()) {
				if (
					$propertyFetch instanceof Node\Expr\PropertyFetch
					&& $propertyFetch->name instanceof Node\Identifier
					&& $propertyFetch->var instanceof Expr\Variable
					&& $propertyFetch->var->name === 'this'
					&& $scope->hasExpressionType(new PropertyInitializationExpr($propertyReflection->getName()))->yes()
				) {
					return $this->generateError(
						$propertyReflection->getNativeType(),
						sprintf(
							'%s %s',
							$this->propertyDescriptor->describeProperty($propertyReflection, $scope, $propertyFetch),
							$operatorDescription,
						),
						static function (Type $type) use ($typeMessageCallback): ?string {
							$originalMessage = $typeMessageCallback($type);
							if ($originalMessage === null) {
								return null;
							}

							if (str_starts_with($originalMessage, 'is not')) {
								return sprintf('%s nor uninitialized', $originalMessage);
							}

							return sprintf('%s and initialized', $originalMessage);
						},
						$identifier,
						'initializedProperty',
					);
				}

				if (!$scope->hasExpressionType($propertyFetch)->yes()) {
					$nativeReflection = $propertyReflection->getNativeReflection();
					if (
						$nativeReflection !== null
						&& !$nativeReflection->getNativeReflection()->hasDefaultValue()
						&& (!$nativeReflection->isPromoted() || (!$nativeReflection->isReadOnly() && !$nativeReflection->isHooked()))
					) {
						return null;
					}
				}
			}

			$propertyDescription = $this->propertyDescriptor->describeProperty($propertyReflection, $scope, $propertyFetch);
			$propertyType = $propertyReflection->getWritableType();
			if ($error !== null) {
				return $innerResult !== null
					? $this->doCheck($innerResult->getIssetabilityDescriptor(), $innerResult->getExpr(), $scope, $mutatingScope, $operatorDescription, $identifier, $typeMessageCallback, $error)
					: $error;
			}
			if (!$this->checkAdvancedIsset) {
				return $innerResult !== null
					? $this->checkUndefinedInner($innerResult, $scope, $mutatingScope, $operatorDescription, $identifier)
					: null;
			}

			$error = $this->generateError(
				$propertyReflection->getWritableType(),
				sprintf('%s (%s) %s', $propertyDescription, $propertyType->describe(VerbosityLevel::typeOnly()), $operatorDescription),
				$typeMessageCallback,
				$identifier,
				'property',
			);

			if ($error !== null && $innerResult !== null) {
				return $this->doCheck($innerResult->getIssetabilityDescriptor(), $innerResult->getExpr(), $scope, $mutatingScope, $operatorDescription, $identifier, $typeMessageCallback, $error);
			}

			return $error;
		}

		if ($error !== null) {
			return $error;
		}

		if (!$this->checkAdvancedIsset) {
			return null;
		}

		$error = $this->generateError(
			$this->treatPhpDocTypesAsCertain ? $scope->getScopeType($expr) : $scope->getScopeNativeType($expr),
			sprintf('Expression %s', $operatorDescription),
			$typeMessageCallback,
			$identifier,
			'expr',
		);
		if ($error !== null) {
			return $error;
		}

		if ($expr instanceof Expr\NullsafePropertyFetch) {
			if ($expr->name instanceof Node\Identifier) {
				return RuleErrorBuilder::message(sprintf('Using nullsafe property access "?->%s" %s is unnecessary. Use -> instead.', $expr->name->name, $operatorDescription))
					->identifier('nullsafe.neverNull')
					->build();
			}

			return RuleErrorBuilder::message(sprintf('Using nullsafe property access "?->(Expression)" %s is unnecessary. Use -> instead.', $operatorDescription))
				->identifier('nullsafe.neverNull')
				->build();
		}

		return null;
	}

	/**
	 * @param ErrorIdentifier $identifier
	 */
	private function checkUndefinedInner(ExpressionResult $inner, Scope $scope, MutatingScope $mutatingScope, string $operatorDescription, string $identifier): ?IdentifierRuleError
	{
		return $this->checkUndefined($inner->getIssetabilityDescriptor(), $inner->getExpr(), $scope, $mutatingScope, $operatorDescription, $identifier);
	}

	/**
	 * @param ErrorIdentifier $identifier
	 */
	private function checkUndefined(?IssetabilityDescriptor $descriptor, Expr $expr, Scope $scope, MutatingScope $mutatingScope, string $operatorDescription, string $identifier): ?IdentifierRuleError
	{
		if ($descriptor !== null && $descriptor->isVariable()) {
			$variableName = $descriptor->getVariableName();
			if ($variableName === null) {
				throw new ShouldNotHappenException();
			}

			$hasVariable = $scope->hasVariableType($variableName);
			if (!$hasVariable->no()) {
				return null;
			}

			return RuleErrorBuilder::message(sprintf('Variable $%s %s is never defined.', $variableName, $operatorDescription))
				->identifier(sprintf('%s.variable', $identifier))
				->build();
		}

		if ($descriptor !== null && $descriptor->isOffset()) {
			$varResult = $descriptor->getVarResult();
			$dimResult = $descriptor->getDimResult();
			if ($varResult === null || $dimResult === null) {
				throw new ShouldNotHappenException();
			}

			$type = $this->treatPhpDocTypesAsCertain ? $varResult->getTypeForScope($mutatingScope) : $varResult->getNativeTypeForScope($mutatingScope);
			$dimType = $this->treatPhpDocTypesAsCertain ? $dimResult->getTypeForScope($mutatingScope) : $dimResult->getNativeTypeForScope($mutatingScope);
			$hasOffsetValue = $type->hasOffsetValueType($dimType);
			if (!$type->isOffsetAccessible()->yes()) {
				return $this->checkUndefinedInner($varResult, $scope, $mutatingScope, $operatorDescription, $identifier);
			}

			if (!$hasOffsetValue->no()) {
				return $this->checkUndefinedInner($varResult, $scope, $mutatingScope, $operatorDescription, $identifier);
			}

			return RuleErrorBuilder::message(
				sprintf(
					'Offset %s on %s %s does not exist.',
					$dimType->describe(VerbosityLevel::value()),
					$type->describe(VerbosityLevel::value()),
					$operatorDescription,
				),
			)->identifier(sprintf('%s.offset', $identifier))->build();
		}

		if ($descriptor !== null && $descriptor->isProperty()) {
			$innerResult = $descriptor->getInnerResult();

			return $innerResult !== null
				? $this->checkUndefinedInner($innerResult, $scope, $mutatingScope, $operatorDescription, $identifier)
				: null;
		}

		return null;
	}

	/**
	 * @param callable(Type): ?string $typeMessageCallback
	 * @param ErrorIdentifier $identifier
	 * @param 'variable'|'offset'|'property'|'expr'|'initializedProperty' $identifierSecondPart
	 */
	private function generateError(Type $type, string $message, callable $typeMessageCallback, string $identifier, string $identifierSecondPart): ?IdentifierRuleError
	{
		$typeMessage = $typeMessageCallback($type);
		if ($typeMessage === null) {
			return null;
		}

		return RuleErrorBuilder::message(
			sprintf('%s %s.', $message, $typeMessage),
		)->identifier(sprintf('%s.%s', $identifier, $identifierSecondPart))->build();
	}

}
