<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use Closure;
use PhpParser\Node\Expr;
use PhpParser\Node\Expr\ArrayDimFetch;
use PhpParser\Node\Expr\List_;
use PhpParser\Node\Expr\PropertyFetch;
use PhpParser\Node\Expr\StaticPropertyFetch;
use PHPStan\Analyser\EnsuredNonNullabilityResult;
use PHPStan\Analyser\EnsuredNonNullabilityResultExpression;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\TrinaryLogic;
use PHPStan\Type\TypeCombinator;

#[AutowiredService]
final class NonNullabilityHelper
{

	public function ensureShallowNonNullability(NodeScopeResolver $nodeScopeResolver, MutatingScope $scope, MutatingScope $originalScope, Expr $exprToSpecify): EnsuredNonNullabilityResult
	{
		// the expression has not been processed into the storage yet (this runs
		// before processExprNode), so read its type from the stored result or
		// price it on demand instead of re-walking via Scope::getType().
		$exprType = $nodeScopeResolver->readStoredOrPriceOnDemand($exprToSpecify, $scope);
		$isNull = $exprType->isNull();
		if ($isNull->yes()) {
			return new EnsuredNonNullabilityResult($scope, []);
		}

		$hasExpressionType = $originalScope->hasExpressionType($exprToSpecify);

		$exprTypeWithoutNull = TypeCombinator::removeNull($exprType);
		if ($exprType->equals($exprTypeWithoutNull)) {
			$originalExprType = $nodeScopeResolver->readStoredOrPriceOnDemand($exprToSpecify, $originalScope);
			if (!$originalExprType->equals($exprTypeWithoutNull)) {
				$originalNativeType = $nodeScopeResolver->readStoredOrPriceOnDemand($exprToSpecify, $originalScope->doNotTreatPhpDocTypesAsCertain());

				return new EnsuredNonNullabilityResult($scope, [
					new EnsuredNonNullabilityResultExpression($exprToSpecify, $originalExprType, $originalNativeType, $hasExpressionType),
				]);
			}
			return new EnsuredNonNullabilityResult($scope, []);
		}

		$specifiedExpressions = [];

		// When narrowing an ArrayDimFetch, specifyExpressionType also recursively
		// narrows the parent array's offset type via intersection with HasOffsetValueType.
		// To properly revert this, we must also save and restore the parent expression's type.
		if ($exprToSpecify instanceof Expr\ArrayDimFetch && $exprToSpecify->dim !== null) {
			$parentExpr = $exprToSpecify->var;
			$specifiedExpressions[] = new EnsuredNonNullabilityResultExpression(
				$parentExpr,
				$nodeScopeResolver->readStoredOrPriceOnDemand($parentExpr, $scope),
				$nodeScopeResolver->readStoredOrPriceOnDemand($parentExpr, $scope->doNotTreatPhpDocTypesAsCertain()),
				$originalScope->hasExpressionType($parentExpr),
			);
		}

		// keep certainty
		$certainty = TrinaryLogic::createYes();
		if (!$hasExpressionType->no()) {
			$certainty = $hasExpressionType;
		}

		$nativeType = $nodeScopeResolver->readStoredOrPriceOnDemand($exprToSpecify, $scope->doNotTreatPhpDocTypesAsCertain());
		$specifiedExpressions[] = new EnsuredNonNullabilityResultExpression($exprToSpecify, $exprType, $nativeType, $certainty);
		$scope = $scope->specifyExpressionType(
			$exprToSpecify,
			$exprTypeWithoutNull,
			TypeCombinator::removeNull($nativeType),
			$certainty,
		);

		return new EnsuredNonNullabilityResult(
			$scope,
			$specifiedExpressions,
		);
	}

	public function ensureNonNullability(NodeScopeResolver $nodeScopeResolver, MutatingScope $scope, Expr $expr): EnsuredNonNullabilityResult
	{
		$specifiedExpressions = [];
		$originalScope = $scope;
		$scope = $this->lookForExpressionCallback($scope, $expr, function ($scope, $expr) use (&$specifiedExpressions, $originalScope, $nodeScopeResolver) {
			$result = $this->ensureShallowNonNullability($nodeScopeResolver, $scope, $originalScope, $expr);
			foreach ($result->getSpecifiedExpressions() as $specifiedExpression) {
				$specifiedExpressions[] = $specifiedExpression;
			}
			return $result->getScope();
		}, false);

		return new EnsuredNonNullabilityResult($scope, $specifiedExpressions);
	}

	/**
	 * @param EnsuredNonNullabilityResultExpression[] $specifiedExpressions
	 */
	public function revertNonNullability(MutatingScope $scope, array $specifiedExpressions): MutatingScope
	{
		foreach ($specifiedExpressions as $specifiedExpressionResult) {
			if ($specifiedExpressionResult->getCertainty()->no()) {
				$scope = $scope->invalidateExpression($specifiedExpressionResult->getExpression());
				continue;
			}
			$scope = $scope->specifyExpressionType(
				$specifiedExpressionResult->getExpression(),
				$specifiedExpressionResult->getOriginalType(),
				$specifiedExpressionResult->getOriginalNativeType(),
				$specifiedExpressionResult->getCertainty(),
			);
		}

		return $scope;
	}

	/**
	 * @param Closure(MutatingScope, Expr): MutatingScope $callback
	 */
	private function lookForExpressionCallback(MutatingScope $scope, Expr $expr, Closure $callback, bool $includeExpr = true): MutatingScope
	{
		// $includeExpr is false only for the outermost operand: ensuring its chain
		// links non-null lets it be walked without spurious "possibly null" noise,
		// but the operand's own value must keep its real (nullable) type - that is
		// the type the isset/empty/?? verdict and narrowing read from its result.
		if ($includeExpr && (!$expr instanceof ArrayDimFetch || $expr->dim !== null)) {
			$scope = $callback($scope, $expr);
		}

		if ($expr instanceof ArrayDimFetch) {
			$scope = $this->lookForExpressionCallback($scope, $expr->var, $callback);
		} elseif ($expr instanceof PropertyFetch || $expr instanceof Expr\NullsafePropertyFetch) {
			$scope = $this->lookForExpressionCallback($scope, $expr->var, $callback);
		} elseif ($expr instanceof StaticPropertyFetch && $expr->class instanceof Expr) {
			$scope = $this->lookForExpressionCallback($scope, $expr->class, $callback);
		} elseif ($expr instanceof List_) {
			foreach ($expr->items as $item) {
				if ($item === null) {
					continue;
				}

				$scope = $this->lookForExpressionCallback($scope, $item->value, $callback);
			}
		}

		return $scope;
	}

}
