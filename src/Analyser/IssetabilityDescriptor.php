<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

use Closure;
use PhpParser\Node\Expr;
use PHPStan\Rules\Properties\FoundPropertyReflection;
use PHPStan\ShouldNotHappenException;
use PHPStan\Type\Type;

/**
 * The inside-out replacement for the AST re-walk in MutatingScope::issetCheck()
 * (and, later, PHPStan\Rules\IssetCheck). Each chain-link ExpressionResult
 * (variable / array dim fetch / property fetch) carries the descriptor for its
 * own link plus references to the child ExpressionResult(s), so isset/empty/??
 * fold the chain by reading already-computed child results instead of
 * re-traversing the AST and re-resolving types/reflections.
 *
 * Per-link types stay scope-recomputed (via the child results' getTypeForScope)
 * because issetCheck answers at the asking scope, with phpdoc or native types
 * depending on the scope.
 */
final class IssetabilityDescriptor
{

	private const KIND_VARIABLE = 'variable';
	private const KIND_OFFSET = 'offset';
	private const KIND_PROPERTY = 'property';

	/**
	 * @param Closure(MutatingScope): ?FoundPropertyReflection|null $reflectionResolver
	 */
	private function __construct(
		private string $kind,
		private ?string $variableName = null,
		private ?ExpressionResult $varResult = null,
		private ?ExpressionResult $dimResult = null,
		private ?ExpressionResult $innerResult = null,
		private ?Closure $reflectionResolver = null,
		private ?Expr $propertyFetch = null,
	)
	{
	}

	public static function variable(string $variableName): self
	{
		return new self(self::KIND_VARIABLE, variableName: $variableName);
	}

	public static function offset(ExpressionResult $varResult, ExpressionResult $dimResult): self
	{
		return new self(self::KIND_OFFSET, varResult: $varResult, dimResult: $dimResult);
	}

	/**
	 * @param Closure(MutatingScope): ?FoundPropertyReflection $reflectionResolver
	 */
	public static function property(?ExpressionResult $innerResult, Closure $reflectionResolver, Expr $propertyFetch): self
	{
		return new self(self::KIND_PROPERTY, innerResult: $innerResult, reflectionResolver: $reflectionResolver, propertyFetch: $propertyFetch);
	}

	/**
	 * @param callable(Type): ?bool $typeCallback
	 */
	public function check(MutatingScope $scope, callable $typeCallback, ?bool $result = null): ?bool
	{
		if ($this->kind === self::KIND_VARIABLE) {
			$variableName = $this->variableName;
			if ($variableName === null) {
				throw new ShouldNotHappenException();
			}

			$hasVariable = $scope->hasVariableType($variableName);
			if ($hasVariable->maybe()) {
				return null;
			}

			if ($result === null) {
				if ($hasVariable->yes()) {
					if ($variableName === '_SESSION') {
						return null;
					}

					return $typeCallback($scope->getVariableType($variableName));
				}

				return false;
			}

			return $result;
		}

		if ($this->kind === self::KIND_OFFSET) {
			$varResult = $this->varResult;
			$dimResult = $this->dimResult;
			if ($varResult === null || $dimResult === null) {
				throw new ShouldNotHappenException();
			}

			$type = $varResult->getTypeForScope($scope);
			if (!$type->isOffsetAccessible()->yes()) {
				return $result ?? $this->checkUndefinedInner($varResult, $scope);
			}

			$dimType = $dimResult->getTypeForScope($scope);
			$hasOffsetValue = $type->hasOffsetValueType($dimType);
			if ($hasOffsetValue->no()) {
				return false;
			}

			// If offset cannot be null, store this error message and see if one of the earlier offsets is.
			// E.g. $array['a']['b']['c'] ?? null; is a valid coalesce if a OR b or C might be null.
			if ($hasOffsetValue->yes()) {
				$result = $typeCallback($type->getOffsetValueType($dimType));

				if ($result !== null) {
					return $this->checkInner($varResult, $scope, $typeCallback, $result);
				}
			}

			// Has offset, it is nullable
			return null;
		}

		$reflectionResolver = $this->reflectionResolver;
		$propertyFetch = $this->propertyFetch;
		if ($reflectionResolver === null || $propertyFetch === null) {
			throw new ShouldNotHappenException();
		}
		$innerResult = $this->innerResult;

		$propertyReflection = $reflectionResolver($scope);
		if ($propertyReflection === null) {
			return $innerResult !== null ? $this->checkUndefinedInner($innerResult, $scope) : null;
		}

		if (!$propertyReflection->isNative()) {
			return $innerResult !== null ? $this->checkUndefinedInner($innerResult, $scope) : null;
		}

		if ($propertyReflection->hasNativeType() && !$propertyReflection->isVirtual()->yes()) {
			if (!$scope->hasExpressionType($propertyFetch)->yes()) {
				$nativeReflection = $propertyReflection->getNativeReflection();
				if ($nativeReflection === null || !$nativeReflection->isPromoted() || (!$nativeReflection->isReadOnly() && !$nativeReflection->isHooked())) {
					return $innerResult !== null ? $this->checkUndefinedInner($innerResult, $scope) : null;
				}
			}
		}

		if ($result !== null) {
			return $innerResult !== null ? $this->checkInner($innerResult, $scope, $typeCallback, $result) : $result;
		}

		$result = $typeCallback($propertyReflection->getWritableType());
		if ($result !== null && $innerResult !== null) {
			return $this->checkInner($innerResult, $scope, $typeCallback, $result);
		}

		return $result;
	}

	public function checkUndefined(MutatingScope $scope): ?bool
	{
		if ($this->kind === self::KIND_VARIABLE) {
			$variableName = $this->variableName;
			if ($variableName === null) {
				throw new ShouldNotHappenException();
			}

			$hasVariable = $scope->hasVariableType($variableName);
			if (!$hasVariable->no()) {
				return null;
			}

			return false;
		}

		if ($this->kind === self::KIND_OFFSET) {
			$varResult = $this->varResult;
			$dimResult = $this->dimResult;
			if ($varResult === null || $dimResult === null) {
				throw new ShouldNotHappenException();
			}

			$type = $varResult->getTypeForScope($scope);
			$dimType = $dimResult->getTypeForScope($scope);
			$hasOffsetValue = $type->hasOffsetValueType($dimType);
			if (!$type->isOffsetAccessible()->yes()) {
				return $this->checkUndefinedInner($varResult, $scope);
			}

			if (!$hasOffsetValue->no()) {
				return $this->checkUndefinedInner($varResult, $scope);
			}

			return false;
		}

		$innerResult = $this->innerResult;

		return $innerResult !== null ? $this->checkUndefinedInner($innerResult, $scope) : null;
	}

	/**
	 * @param callable(Type): ?bool $typeCallback
	 */
	private function checkInner(ExpressionResult $inner, MutatingScope $scope, callable $typeCallback, ?bool $result): ?bool
	{
		$innerDescriptor = $inner->getIssetabilityDescriptor();
		if ($innerDescriptor !== null) {
			return $innerDescriptor->check($scope, $typeCallback, $result);
		}

		return $result ?? $typeCallback($inner->getTypeForScope($scope));
	}

	private function checkUndefinedInner(ExpressionResult $inner, MutatingScope $scope): ?bool
	{
		$innerDescriptor = $inner->getIssetabilityDescriptor();
		if ($innerDescriptor !== null) {
			return $innerDescriptor->checkUndefined($scope);
		}

		return null;
	}

}
