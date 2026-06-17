<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\PropertyFetch;
use PhpParser\Node\Identifier;
use PhpParser\Node\Scalar\String_;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\InternalThrowPoint;
use PHPStan\Analyser\IssetabilityDescriptor;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Php\PhpVersion;
use PHPStan\Rules\Properties\FoundPropertyReflection;
use PHPStan\Rules\Properties\PropertyReflectionFinder;
use PHPStan\Type\ErrorType;
use PHPStan\Type\MixedType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use function array_map;
use function array_merge;
use function count;

/**
 * @implements ExprHandler<PropertyFetch>
 */
#[AutowiredService]
final class PropertyFetchHandler implements ExprHandler
{

	public function __construct(
		private PhpVersion $phpVersion,
		private PropertyReflectionFinder $propertyReflectionFinder,
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof PropertyFetch;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		$scopeBeforeVar = $scope;
		$varResult = $nodeScopeResolver->processExprNode($stmt, $expr->var, $scope, $storage, $nodeCallback, $context->enterDeep());
		$hasYield = $varResult->hasYield();
		$throwPoints = $varResult->getThrowPoints();
		$impurePoints = $varResult->getImpurePoints();
		$isAlwaysTerminating = $varResult->isAlwaysTerminating();
		$scope = $varResult->getScope();
		$nameResult = null;
		if ($expr->name instanceof Identifier) {
			$propertyName = $expr->name->toString();
			$propertyHolderType = $scopeBeforeVar->getType($expr->var);
			$propertyReflection = $scopeBeforeVar->getInstancePropertyReflection($propertyHolderType, $propertyName);
			if ($propertyReflection !== null && $this->phpVersion->supportsPropertyHooks()) {
				$propertyDeclaringClass = $propertyReflection->getDeclaringClass();
				if ($propertyDeclaringClass->hasNativeProperty($propertyName)) {
					$nativeProperty = $propertyDeclaringClass->getNativeProperty($propertyName);
					$throwPoints = array_merge($throwPoints, $nodeScopeResolver->getThrowPointsFromPropertyHook($scopeBeforeVar, $expr, $nativeProperty, 'get'));
				}
			}
		} else {
			$nameResult = $nodeScopeResolver->processExprNode($stmt, $expr->name, $scope, $storage, $nodeCallback, $context->enterDeep());
			$hasYield = $hasYield || $nameResult->hasYield();
			$throwPoints = array_merge($throwPoints, $nameResult->getThrowPoints());
			$impurePoints = array_merge($impurePoints, $nameResult->getImpurePoints());
			$isAlwaysTerminating = $isAlwaysTerminating || $nameResult->isAlwaysTerminating();
			$scope = $nameResult->getScope();
			if ($this->phpVersion->supportsPropertyHooks()) {
				$throwPoints[] = InternalThrowPoint::createImplicit($scope, $expr);
			}
		}

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $hasYield,
			isAlwaysTerminating: $isAlwaysTerminating,
			throwPoints: $throwPoints,
			impurePoints: $impurePoints,
			containsNullsafe: $varResult->containsNullsafe(),
			issetabilityDescriptor: IssetabilityDescriptor::property($varResult, fn (MutatingScope $s): ?FoundPropertyReflection => $this->propertyReflectionFinder->findPropertyReflectionFromNode($expr, $s), $expr),
			typeCallback: function (MutatingScope $s) use ($expr, $varResult, $nameResult): Type {
				// a fetch on a nullsafe chain whose receiver is currently nullable
				// short-circuits to null - the receiver result carries whether the
				// chain contains a ?-> (a plain nullable receiver does not propagate)
				$shortCircuit = static fn (Type $type): Type => $varResult->containsNullsafe() && TypeCombinator::containsNull($varResult->getTypeForScope($s))
					? TypeCombinator::addNull($type)
					: $type;

				if ($expr->name instanceof Identifier) {
					if ($s->nativeTypesPromoted) {
						$propertyReflection = $this->propertyReflectionFinder->findPropertyReflectionFromNode($expr, $s);
						if ($propertyReflection === null) {
							return new ErrorType();
						}

						if (!$propertyReflection->hasNativeType()) {
							return new MixedType();
						}

						return $shortCircuit($propertyReflection->getNativeType());
					}

					$returnType = $this->propertyFetchType(
						$s,
						$varResult->getTypeForScope($s),
						$expr->name->name,
						$expr,
					);
					if ($returnType === null) {
						$returnType = new ErrorType();
					}

					return $shortCircuit($returnType);
				}

				$nameType = $nameResult !== null ? $nameResult->getTypeForScope($s) : $s->getType($expr->name);
				if (count($nameType->getConstantStrings()) > 0) {
					return TypeCombinator::union(
						...array_map(static fn ($constantString) => $constantString->getValue() === '' ? new ErrorType() : $s
							->filterByTruthyValue(new Expr\BinaryOp\Identical($expr->name, new String_($constantString->getValue())))
							->getType(
								new PropertyFetch($expr->var, new Identifier($constantString->getValue())),
							), $nameType->getConstantStrings()),
					);
				}

				return new MixedType();
			},
			specifyTypesCallback: fn (MutatingScope $s, TypeSpecifierContext $context): SpecifiedTypes => $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context),
		);
	}

	private function propertyFetchType(MutatingScope $scope, Type $fetchedOnType, string $propertyName, PropertyFetch $propertyFetch): ?Type
	{
		$propertyReflection = $scope->getInstancePropertyReflection($fetchedOnType, $propertyName);
		if ($propertyReflection === null) {
			return null;
		}

		if ($scope->isInWriteExpressionAssign($propertyFetch)) {
			return $propertyReflection->getWritableType();
		}

		return $propertyReflection->getReadableType();
	}

}
