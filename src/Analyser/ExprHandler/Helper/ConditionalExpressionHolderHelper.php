<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\BooleanAnd;
use PhpParser\Node\Expr\BinaryOp\BooleanOr;
use PhpParser\Node\Expr\BinaryOp\LogicalAnd;
use PhpParser\Node\Expr\BinaryOp\LogicalOr;
use PHPStan\Analyser\ConditionalExpressionHolderRecipe;
use PHPStan\Analyser\DisjunctionBranchUnionAugment;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\DependencyInjection\AutowiredService;
use function is_string;

/**
 * Builds the conditional-expression-holder recipes used to project narrowings
 * of boolean operands (`&&`, `||`) into later scopes. Shared by
 * BooleanAndHandler and BooleanOrHandler.
 */
#[AutowiredService]
final class ConditionalExpressionHolderHelper
{

	public function __construct(
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	/**
	 * Captures the either-branch union recovery as a deferred augment: the
	 * branch types are read from the operand-walk filtered scopes here at
	 * compose time, while the does-it-actually-narrow gates run against the
	 * applying scope when MutatingScope::applySpecifiedTypes() evaluates it.
	 */
	public function buildBranchUnionAugment(
		NodeScopeResolver $nodeScopeResolver,
		SpecifiedTypes $leftTypes,
		SpecifiedTypes $rightTypes,
		MutatingScope $leftFilteredScope,
		MutatingScope $rightFilteredScope,
		SpecifiedTypes $types,
	): ?DisjunctionBranchUnionAugment
	{
		$candidateExprs = [];
		foreach ($leftTypes->getSureTypes() as $exprString => [$exprNode, $type]) {
			$candidateExprs[$exprString] = $exprNode;
		}
		foreach ($rightTypes->getSureTypes() as $exprString => [$exprNode, $type]) {
			$candidateExprs[$exprString] = $exprNode;
		}

		$existingSureTypes = $types->getSureTypes();
		$existingAlternativeTypes = $types->getAlternativeTypes();

		$candidates = [];
		foreach ($candidateExprs as $exprString => $targetExpr) {
			if (isset($existingSureTypes[$exprString])) {
				continue;
			}
			// the exact either-branch merge already constrains this expression
			// (an alternative-form entry) - the branch-scope union recovery
			// would only add a weaker entry on top
			if (isset($existingAlternativeTypes[$exprString])) {
				continue;
			}
			if (!$leftFilteredScope->hasExpressionType($targetExpr)->yes()) {
				continue;
			}
			if (!$rightFilteredScope->hasExpressionType($targetExpr)->yes()) {
				continue;
			}

			// the operands were processed during processExpr; read their stored
			// results on these filtered scopes instead of re-walking via getType().
			$candidates[] = [
				$targetExpr,
				$nodeScopeResolver->readTypeOfMaybeStored($targetExpr, $leftFilteredScope),
				$nodeScopeResolver->readTypeOfMaybeStored($targetExpr, $rightFilteredScope),
			];
		}

		if ($candidates === []) {
			return null;
		}

		return new DisjunctionBranchUnionAugment($nodeScopeResolver, $this->defaultNarrowingHelper, $candidates);
	}

	/**
	 * Captures the raw entries of a boolean-decomposition holder pair as a
	 * recipe; the state-dependent complement/target math runs against the
	 * applying scope when MutatingScope::applySpecifiedTypes() evaluates it.
	 *
	 * The condition side asserts that its sub-expression evaluates truthy.
	 * When that sub-expression is itself a compound boolean (e.g. `$a && $b`),
	 * the narrowings making it true are spread across both the sure and
	 * sureNot lists of its specification. All of them are conjuncts of the
	 * single "this side is true" condition, so they must be gathered together
	 * into one condition set. Picking only one list would drop a conjunct and
	 * let the resulting holder fire too eagerly.
	 *
	 * @param MutatingScope|null $nonVariableTargetScope the operand-walk scope non-variable
	 *        holder targets were tracked on; their types are pinned from it at compose
	 *        time (null = read every target from the applying scope)
	 */
	public function buildConditionalHolderRecipe(SpecifiedTypes $conditionSpecifiedTypes, SpecifiedTypes $holderSpecifiedTypes, bool $holdersFromSureTypes, bool $holderSideIsNegated, ?MutatingScope $nonVariableTargetScope, ?Expr $holderSideExpr = null): ?ConditionalExpressionHolderRecipe
	{
		// an alternative-form entry (a cross-kind either-branch merge) has no
		// single condition type; dropping it from the condition set would let
		// the holder fire too eagerly - build no holders from such a condition
		if ($conditionSpecifiedTypes->getAlternativeTypes() !== []) {
			return null;
		}

		// A holder side that is itself a compound boolean cannot always be split
		// into independent per-expression holders. In the `BooleanAnd` false
		// context the holder asserts its side is false: when that side is a
		// conjunction (`$a && $b`), its negation is the disjunction `!$a || !$b`,
		// which has no per-expression narrowing — narrowing each conjunct
		// independently would drop a reachable value (e.g. `$a = false, $b = true`).
		// Symmetrically, in the `BooleanOr` true context the holder asserts its
		// side is true, and a disjunction side (`$a || $b`) is itself a disjunction.
		// Such a side is left whole rather than split into over-narrowing holders.
		if ($this->isUnsplittableCompoundHolderSide($holderSideExpr, $holderSideIsNegated)) {
			return null;
		}

		$conditionEntries = [];
		foreach ($conditionSpecifiedTypes->getSureTypes() as $exprString => [$expr, $type]) {
			if (!$this->isTrackableExpression($expr)) {
				continue;
			}

			$conditionEntries[] = [(string) $exprString, $expr, true, $type];
		}
		foreach ($conditionSpecifiedTypes->getSureNotTypes() as $exprString => [$expr, $type]) {
			if (!$this->isTrackableExpression($expr)) {
				continue;
			}

			$conditionEntries[] = [(string) $exprString, $expr, false, $type];
		}

		if ($conditionEntries === []) {
			return null;
		}

		$holderEntries = [];
		$holderTypes = $holdersFromSureTypes ? $holderSpecifiedTypes->getSureTypes() : $holderSpecifiedTypes->getSureNotTypes();
		foreach ($holderTypes as $exprString => [$expr, $type]) {
			if (!$this->isTrackableExpression($expr)) {
				continue;
			}

			$pinnedTargetType = !$expr instanceof Expr\Variable && $nonVariableTargetScope !== null
				? $nonVariableTargetScope->getStateType($expr)
				: null;
			$holderEntries[] = [(string) $exprString, $expr, $type, $pinnedTargetType];
		}

		if ($holderEntries === []) {
			return null;
		}

		return new ConditionalExpressionHolderRecipe($conditionEntries, $holderEntries, $holdersFromSureTypes);
	}

	/**
	 * A holder side whose truth value is asserted as a disjunction cannot be
	 * decomposed into independent per-expression holders. That happens for a
	 * conjunction (`&&`) asserted false (negated context) and for a disjunction
	 * (`||`) asserted true.
	 */
	private function isUnsplittableCompoundHolderSide(?Expr $holderSideExpr, bool $holderSideIsNegated): bool
	{
		if ($holderSideExpr === null) {
			return false;
		}

		if ($holderSideIsNegated) {
			return $holderSideExpr instanceof BooleanAnd || $holderSideExpr instanceof LogicalAnd;
		}

		return $holderSideExpr instanceof BooleanOr || $holderSideExpr instanceof LogicalOr;
	}

	private function isTrackableExpression(Expr $expr): bool
	{
		if ($expr instanceof Expr\Variable) {
			return is_string($expr->name);
		}

		return $expr instanceof Expr\PropertyFetch
			|| $expr instanceof Expr\ArrayDimFetch
			|| $expr instanceof Expr\StaticPropertyFetch;
	}

}
