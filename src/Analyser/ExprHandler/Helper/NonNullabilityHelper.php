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
use PHPStan\Node\Printer\ExprPrinter;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\TrinaryLogic;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use function array_pop;
use function count;

#[AutowiredService]
final class NonNullabilityHelper
{

	/**
	 * The ensures currently in effect during the walk, innermost last. An
	 * ensure writes non-null "device" types into the scope so nested fetches
	 * walk without spurious possibly-null noise - indistinguishable from
	 * genuine narrowing in scope state. Handlers whose semantics depend on an
	 * expression's REAL nullability (a nullsafe operator's short-circuit)
	 * consult this stack for the pre-device type instead.
	 *
	 * @var list<array<string, array{Type, Type}>>
	 */
	private array $activeEnsures = [];

	public function __construct(private ExprPrinter $exprPrinter)
	{
	}

	/**
	 * The pre-device type an active ensure saved for this expression, or null
	 * when no ensure covers it.
	 */
	public function getActiveEnsuredOriginalType(Expr $expr, bool $native): ?Type
	{
		if ($this->activeEnsures === []) {
			return null;
		}

		$key = $this->exprPrinter->printExpr($expr);
		for ($i = count($this->activeEnsures) - 1; $i >= 0; $i--) {
			if (isset($this->activeEnsures[$i][$key])) {
				return $this->activeEnsures[$i][$key][$native ? 1 : 0];
			}
		}

		return null;
	}

	public function ensureShallowNonNullability(MutatingScope $scope, MutatingScope $originalScope, Expr $exprToSpecify): EnsuredNonNullabilityResult
	{
		$result = $this->doEnsureShallowNonNullability($scope, $originalScope, $exprToSpecify);
		$this->pushActiveEnsure($result);

		return $result;
	}

	private function pushActiveEnsure(EnsuredNonNullabilityResult $result): void
	{
		$originals = [];
		foreach ($result->getSpecifiedExpressions() as $specifiedExpression) {
			$originals[$this->exprPrinter->printExpr($specifiedExpression->getExpression())] = [
				$specifiedExpression->getOriginalType(),
				$specifiedExpression->getOriginalNativeType(),
			];
		}
		$this->activeEnsures[] = $originals;
	}

	private function doEnsureShallowNonNullability(MutatingScope $scope, MutatingScope $originalScope, Expr $exprToSpecify): EnsuredNonNullabilityResult
	{
		// the expression has not been processed into the storage yet (this runs
		// before processExprNode) - derive its current type from the scope's
		// tracked state. A non-narrowable subject (a call, a fresh fetch) has no
		// tracked state and must be priced before its walk BY DESIGN: the device
		// this ensure writes is what the walk runs on - a sanctioned read.
		$exprType = NodeScopeResolver::sanctionedGuardRead(static fn (): Type => $scope->getStateType($exprToSpecify));
		$isNull = $exprType->isNull();
		if ($isNull->yes()) {
			return new EnsuredNonNullabilityResult($scope, []);
		}

		$hasExpressionType = $originalScope->hasExpressionType($exprToSpecify);

		$exprTypeWithoutNull = TypeCombinator::removeNull($exprType);
		if ($exprType->equals($exprTypeWithoutNull)) {
			$originalExprType = NodeScopeResolver::sanctionedGuardRead(static fn (): Type => $originalScope->getStateType($exprToSpecify));
			if (!$originalExprType->equals($exprTypeWithoutNull)) {
				$originalNativeType = NodeScopeResolver::sanctionedGuardRead(static fn (): Type => $originalScope->doNotTreatPhpDocTypesAsCertain()->getStateType($exprToSpecify));

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
				NodeScopeResolver::sanctionedGuardRead(static fn (): Type => $scope->getStateType($parentExpr)),
				NodeScopeResolver::sanctionedGuardRead(static fn (): Type => $scope->doNotTreatPhpDocTypesAsCertain()->getStateType($parentExpr)),
				$originalScope->hasExpressionType($parentExpr),
			);
		}

		// keep certainty
		$certainty = TrinaryLogic::createYes();
		if (!$hasExpressionType->no()) {
			$certainty = $hasExpressionType;
		}

		$nativeType = NodeScopeResolver::sanctionedGuardRead(static fn (): Type => $scope->doNotTreatPhpDocTypesAsCertain()->getStateType($exprToSpecify));
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

	public function ensureNonNullability(MutatingScope $scope, Expr $expr): EnsuredNonNullabilityResult
	{
		$specifiedExpressions = [];
		$originalScope = $scope;
		$scope = $this->lookForExpressionCallback($scope, $expr, function ($scope, $expr) use (&$specifiedExpressions, $originalScope) {
			$result = $this->doEnsureShallowNonNullability($scope, $originalScope, $expr);
			foreach ($result->getSpecifiedExpressions() as $specifiedExpression) {
				$specifiedExpressions[] = $specifiedExpression;
			}
			return $result->getScope();
		}, false);

		$result = new EnsuredNonNullabilityResult($scope, $specifiedExpressions);
		$this->pushActiveEnsure($result);

		return $result;
	}

	/**
	 * @param EnsuredNonNullabilityResultExpression[] $specifiedExpressions
	 */
	public function revertNonNullability(MutatingScope $scope, array $specifiedExpressions): MutatingScope
	{
		array_pop($this->activeEnsures);
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
