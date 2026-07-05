<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use PhpParser\Node\Expr;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use function is_string;

/**
 * The conjunction narrowing - BooleanAnd's specify semantics - composed from
 * per-operand narrowing closures and branch scopes instead of the operands'
 * ExpressionResults, so conjunctions without an AST node (the falsy fold of
 * a multi-subject isset()) reuse it without synthesizing BooleanAnd chains.
 */
#[AutowiredService]
final class BooleanNarrowingHelper
{

	public function __construct(
		private ConditionalExpressionHolderHelper $conditionalExpressionHolderHelper,
	)
	{
	}

	/**
	 * @param callable(MutatingScope, TypeSpecifierContext): SpecifiedTypes $leftTypesCallback
	 * @param callable(MutatingScope, TypeSpecifierContext): SpecifiedTypes $rightTypesCallback
	 */
	public function specifyConjunction(
		NodeScopeResolver $nodeScopeResolver,
		MutatingScope $s,
		TypeSpecifierContext $context,
		Expr $rootExpr,
		Expr $leftExpr,
		callable $leftTypesCallback,
		MutatingScope $leftTruthyScope,
		MutatingScope $leftFalseyScope,
		Expr $rightExpr,
		callable $rightTypesCallback,
		MutatingScope $rightFalseyScope,
	): SpecifiedTypes
	{
			$leftTypes = $leftTypesCallback($s, $context)->setRootExpr($rootExpr);
			$rightScope = $leftTruthyScope;
			$rightTypes = $rightTypesCallback($s, $context)->setRootExpr($rootExpr);
			if ($context->true()) {
				$types = $leftTypes->unionWith($rightTypes);
			} else {
				$leftNormalized = $leftTypes->normalize($s, $nodeScopeResolver);
				$rightNormalized = $rightTypes->normalize($rightScope, $nodeScopeResolver);
				$types = $leftNormalized->intersectWith($rightNormalized);
				$types = $this->conditionalExpressionHolderHelper->augmentDisjunctionTypes($nodeScopeResolver, $s, $leftNormalized, $rightNormalized, $leftFalseyScope, $rightFalseyScope, $types);
			}
			if ($context->false()) {
				// Consequent (holder) narrowings projected by each holder: these must be
				// the genuine falsey narrowing of the arm. When that is empty, the arm
				// has no sound falsey narrowing and must not contribute a consequent.
				$leftHolderTypes = $leftTypes;
				$rightHolderTypes = $rightTypes;
				// In a mixed truthy-and-false context, re-derive empty holders from the falsey narrowing.
				if ($context->truthy()) {
					if ($leftHolderTypes->getSureTypes() === [] && $leftHolderTypes->getSureNotTypes() === []) {
						$leftHolderTypes = $leftTypesCallback($s, TypeSpecifierContext::createFalsey())->setRootExpr($rootExpr);
					}
					if ($rightHolderTypes->getSureTypes() === [] && $rightHolderTypes->getSureNotTypes() === []) {
						$rightHolderTypes = $rightTypesCallback($rightScope, TypeSpecifierContext::createFalsey())->setRootExpr($rootExpr);
					}
				}
				// Condition (antecedent) narrowings: when an arm has no falsey narrowing
				// (e.g. isset() on an array dim fetch), derive the condition from the truthy
				// narrowing by swapping sure/sureNot types. This swap is only sound for the
				// antecedent — processBooleanConditionalTypes inverts it back to the truthy
				// narrowing. It must NOT feed the consequent: inverting a comparison's truthy
				// narrowing (e.g. `$a === $b` narrowing `$a` to `$b`'s broad type) would
				// over-narrow the consequent (see regression for `$x === $nonConstantString`).
				$leftCondTypes = $leftHolderTypes;
				$rightCondTypes = $rightHolderTypes;
				if ($leftCondTypes->getSureTypes() === [] && $leftCondTypes->getSureNotTypes() === []) {
					$truthyLeftTypes = $leftTypesCallback($s, TypeSpecifierContext::createTruthy());
					if ($this->allExpressionsTrackable($truthyLeftTypes)) {
						$leftCondTypes = new SpecifiedTypes($truthyLeftTypes->getSureNotTypes(), $truthyLeftTypes->getSureTypes());
					}
				}
				if ($rightCondTypes->getSureTypes() === [] && $rightCondTypes->getSureNotTypes() === []) {
					$truthyRightTypes = $rightTypesCallback($rightScope, TypeSpecifierContext::createTruthy());
					if ($this->allExpressionsTrackable($truthyRightTypes)) {
						$rightCondTypes = new SpecifiedTypes($truthyRightTypes->getSureNotTypes(), $truthyRightTypes->getSureTypes());
					}
				}
				$result = new SpecifiedTypes(
					$types->getSureTypes(),
					$types->getSureNotTypes(),
				);
				if ($types->shouldOverwrite()) {
					$result = $result->setAlwaysOverwriteTypes();
				}
				return $result->setNewConditionalExpressionHolders($this->conditionalExpressionHolderHelper->mergeConditionalHolders([
					$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $leftCondTypes, $rightHolderTypes, false, true, $rightScope, $rightExpr),
					$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $rightCondTypes, $leftHolderTypes, false, true, $s, $leftExpr),
					$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $leftCondTypes, $rightHolderTypes, true, true, $rightScope, $rightExpr),
					$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $rightCondTypes, $leftHolderTypes, true, true, $s, $leftExpr),
				]))->setRootExpr($rootExpr);
			}

			return $types;
	}

	private function allExpressionsTrackable(SpecifiedTypes $types): bool
	{
		foreach ($types->getSureTypes() as [$expr]) {
			if (!$this->isTrackableExpression($expr)) {
				return false;
			}
		}
		foreach ($types->getSureNotTypes() as [$expr]) {
			if (!$this->isTrackableExpression($expr)) {
				return false;
			}
		}

		return $types->getSureTypes() !== [] || $types->getSureNotTypes() !== [];
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
