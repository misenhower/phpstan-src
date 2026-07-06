<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use PhpParser\Node\Expr;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\Type\TypeCombinator;
use PHPStan\Type\Type;
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
		private DefaultNarrowingHelper $defaultNarrowingHelper,
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
			// the right operand lives after the left is known true - its narrowing
			// bases read from the left-truthy view, never the raw ask scope
			$rightScope = $leftTruthyScope;
			$rightTypes = $rightTypesCallback($rightScope, $context)->setRootExpr($rootExpr);
			if ($context->true()) {
				$types = $leftTypes->unionWith($rightTypes);
			} else {
				$types = $leftTypes->intersectWith($rightTypes);
				$types = $this->conditionalExpressionHolderHelper->augmentDisjunctionTypes($nodeScopeResolver, $s, $leftTypes, $rightTypes, $leftFalseyScope, $rightFalseyScope, $types);
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
				$result = (new SpecifiedTypes(
					$types->getSureTypes(),
					$types->getSureNotTypes(),
				))->withAlternativeTypesOf($types);
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

	/**
	 * The disjunction narrowing - BooleanOr's specify semantics - composed
	 * from per-operand narrowing/type closures and branch scopes instead of
	 * the operands' ExpressionResults, so disjunctions without an AST node
	 * (the non-null narrowing of empty()) reuse it without synthesizing
	 * BooleanOr chains.
	 *
	 * @param callable(MutatingScope, TypeSpecifierContext): SpecifiedTypes $leftTypesCallback
	 * @param callable(MutatingScope): Type $leftTypeCallback
	 * @param callable(MutatingScope, TypeSpecifierContext): SpecifiedTypes $rightTypesCallback
	 * @param callable(MutatingScope): Type $rightTypeCallback
	 */
	public function specifyDisjunction(
		NodeScopeResolver $nodeScopeResolver,
		MutatingScope $s,
		TypeSpecifierContext $context,
		Expr $rootExpr,
		Expr $leftExpr,
		callable $leftTypesCallback,
		callable $leftTypeCallback,
		MutatingScope $leftTruthyScope,
		MutatingScope $leftFalseyScope,
		Expr $rightExpr,
		callable $rightTypesCallback,
		callable $rightTypeCallback,
		MutatingScope $rightTruthyScope,
	): SpecifiedTypes
	{
			$leftTypes = $leftTypesCallback($s, $context)->setRootExpr($rootExpr);
			$rightScope = $leftFalseyScope;
			$rightTypes = $rightTypesCallback($rightScope, $context)->setRootExpr($rootExpr);


			if ($context->true()) {
				if (
					$leftTypeCallback($s)->toBoolean()->isFalse()->yes()
				) {
					$types = $rightTypes;
				} elseif (
					$leftTypeCallback($s)->toBoolean()->isTrue()->yes()
					|| $rightTypeCallback($s)->toBoolean()->isFalse()->yes()
				) {
					$types = $leftTypes;
				} else {
					$types = $leftTypes->intersectWith($rightTypes);
					$types = $this->augmentDisjunctionTruthyWithConditionalHolders(
						$nodeScopeResolver,
						$s,
						$leftTruthyScope,
						$rightScope,
						$rightTruthyScope,
						$rootExpr,
						$types);
					$types = $this->conditionalExpressionHolderHelper->augmentDisjunctionTypes($nodeScopeResolver, $s, $leftTypes, $rightTypes, $leftTruthyScope, $rightTruthyScope, $types);
				}
			} else {
				$types = $leftTypes->unionWith($rightTypes);
			}

			if ($context->true()) {
				$result = (new SpecifiedTypes(
					$types->getSureTypes(),
					$types->getSureNotTypes(),
				))->withAlternativeTypesOf($types);
				if ($types->shouldOverwrite()) {
					$result = $result->setAlwaysOverwriteTypes();
				}
				return $result->setNewConditionalExpressionHolders($this->conditionalExpressionHolderHelper->mergeConditionalHolders([
					$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $leftTypes, $rightTypes, false, false, $rightScope, $rightExpr),
					$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $rightTypes, $leftTypes, false, false, $s, $leftExpr),
					$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $leftTypes, $rightTypes, true, false, $rightScope, $rightExpr),
					$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $rightTypes, $leftTypes, true, false, $s, $leftExpr),
				]))->setRootExpr($rootExpr);
			}

			return $types;
	}

	private function augmentDisjunctionTruthyWithConditionalHolders(
		NodeScopeResolver $nodeScopeResolver,
		MutatingScope $scope,
		MutatingScope $leftTruthyScope,
		MutatingScope $rightScope,
		MutatingScope $rightTruthyScope,
		Expr $rootExpr,
		SpecifiedTypes $types,
	): SpecifiedTypes
	{
		$seen = [];
		foreach ([$scope, $rightScope] as $sourceScope) {
			foreach ($sourceScope->getConditionalExpressions() as $rootExprString => $holders) {
				if (isset($seen[$rootExprString])) {
					continue;
				}
				if ($holders === []) {
					continue;
				}
				$seen[$rootExprString] = true;
				$targetExpr = $holders[array_key_first($holders)]->getTypeHolder()->getExpr();

				// the exact either-branch merge already constrains this
				// expression - do not add the weaker branch-scope union on top
				if (isset($types->getAlternativeTypes()[$rootExprString])) {
					continue;
				}

				// Only project when the target stays Yes-defined in the original
				// scope and in both filtered branches. A sure type implicitly
				// raises certainty to Yes, which would wrongly upgrade Maybe-defined
				// variables — `if (empty($a['bar']))` for instance leaves `$a`
				// Maybe-defined because `empty()` tolerates undefined offsets.
				if (!$scope->hasExpressionType($targetExpr)->yes()) {
					continue;
				}
				if (!$leftTruthyScope->hasExpressionType($targetExpr)->yes()) {
					continue;
				}
				if (!$rightTruthyScope->hasExpressionType($targetExpr)->yes()) {
					continue;
				}

				$origType = $nodeScopeResolver->readTypeOfMaybeStored($targetExpr, $scope);
				$leftType = $nodeScopeResolver->readTypeOfMaybeStored($targetExpr, $leftTruthyScope);
				$rightType = $nodeScopeResolver->readTypeOfMaybeStored($targetExpr, $rightTruthyScope);

				$leftNarrowed = !$leftType->equals($origType) && $origType->isSuperTypeOf($leftType)->yes();
				$rightNarrowed = !$rightType->equals($origType) && $origType->isSuperTypeOf($rightType)->yes();

				if (!$leftNarrowed || !$rightNarrowed) {
					continue;
				}

				$unionType = TypeCombinator::union($leftType, $rightType);
				if ($unionType->equals($origType)) {
					continue;
				}

				$types = $types->unionWith(
					$this->defaultNarrowingHelper->createSubjectTypes($scope, $targetExpr, null, $unionType, TypeSpecifierContext::createTrue()),
				);
			}
		}

		return $types;
	}

	private function allExpressionsTrackable(SpecifiedTypes $types): bool
	{
		// an alternative-form entry has no single condition type to track
		if ($types->getAlternativeTypes() !== []) {
			return false;
		}

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
