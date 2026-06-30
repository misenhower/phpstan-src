<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\BooleanOr;
use PhpParser\Node\Expr\BinaryOp\LogicalOr;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\ConditionalExpressionHolderHelper;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\BooleanOrNode;
use PHPStan\Type\BooleanType;
use PHPStan\Type\Constant\ConstantBooleanType;
use PHPStan\Type\NeverType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use function array_key_first;
use function array_key_last;
use function array_merge;

/**
 * @implements ExprHandler<BooleanOr|LogicalOr>
 */
#[AutowiredService]
final class BooleanOrHandler implements ExprHandler
{

	public function __construct(
		private ConditionalExpressionHolderHelper $conditionalExpressionHolderHelper,
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof BooleanOr || $expr instanceof LogicalOr;
	}

	/**
	 * For `if ($a || $b)` truthy, expressions narrowed by stored conditional
	 * holders (e.g. `$a = $obj instanceof ClassA;` records "when `$a` is
	 * truthy, `$obj` is `ClassA`") need to be projected into the OR-truthy
	 * scope as the union of the per-arm narrowings. specifyTypesInCondition
	 * for each arm only looks at the boolean variable itself, so the held
	 * narrowing of `$obj` would otherwise be invisible until a later check
	 * pins one of the booleans down.
	 *
	 * For each conditional-holder target $T:
	 * - resolve $T's type in the left-truthy and right-truthy filtered scopes
	 * - if both narrow $T strictly below the original, add `$T : leftT|rightT`
	 *   as a sure type to the OR-truthy result
	 *
	 * The asymmetric case (one arm narrows, the other doesn't) is intentionally
	 * skipped: in the OR-truthy scope the arm that didn't narrow could still be
	 * the truthy one, so the sound result is the original (unnarrowed) type.
	 */
	private function augmentBooleanOrTruthyWithConditionalHolders(
		NodeScopeResolver $nodeScopeResolver,
		MutatingScope $scope,
		MutatingScope $leftTruthyScope,
		MutatingScope $rightScope,
		MutatingScope $rightTruthyScope,
		BooleanOr|LogicalOr $expr,
		SpecifiedTypes $types,
	): SpecifiedTypes
	{
		$seen = [];
		foreach ([$scope, $rightScope] as $sourceScope) {
			foreach ($sourceScope->getConditionalExpressions() as $exprString => $holders) {
				if (isset($seen[$exprString])) {
					continue;
				}
				if ($holders === []) {
					continue;
				}
				$seen[$exprString] = true;
				$targetExpr = $holders[array_key_first($holders)]->getTypeHolder()->getExpr();

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

				$origType = $nodeScopeResolver->readStoredOrPriceOnDemand($targetExpr, $scope);
				$leftType = $nodeScopeResolver->readStoredOrPriceOnDemand($targetExpr, $leftTruthyScope);
				$rightType = $nodeScopeResolver->readStoredOrPriceOnDemand($targetExpr, $rightTruthyScope);

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

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$leftResult = $nodeScopeResolver->processExprNode($stmt, $expr->left, $scope, $storage, $nodeCallback, $context->enterDeep());
		$leftFalseyScope = $leftResult->getFalseyScope();
		$rightResult = $nodeScopeResolver->processExprNode($stmt, $expr->right, $leftFalseyScope, $storage, $nodeCallback, $context);
		$rightExprType = $rightResult->getTypeForScope($rightResult->getScope());
		if ($rightExprType instanceof NeverType && $rightExprType->isExplicit()) {
			$leftMergedWithRightScope = $leftResult->getTruthyScope();
		} else {
			$leftMergedWithRightScope = $leftResult->getScope()->mergeWith($rightResult->getScope());
		}

		$nodeScopeResolver->callNodeCallbackWithExpression($nodeCallback, new BooleanOrNode($expr, $leftFalseyScope), $scope, $storage, $context);

		return $this->expressionResultFactory->create(
			$leftMergedWithRightScope,
			beforeScope: $scope,
			expr: $expr,
			hasYield: $leftResult->hasYield() || $rightResult->hasYield(),
			isAlwaysTerminating: $leftResult->isAlwaysTerminating(),
			throwPoints: array_merge($leftResult->getThrowPoints(), $rightResult->getThrowPoints()),
			impurePoints: array_merge($leftResult->getImpurePoints(), $rightResult->getImpurePoints()),
			// || is falsey only when the right side was evaluated (on the left-falsey
			// scope) and is itself falsey - that is exactly the right operand's falsey
			// scope: it carries the left narrowing and the right's by-ref/side-effect
			// definitions, and does not re-apply the left narrowing over a variable the
			// right operand reassigned (bug-9400).
			falseyScopeOverride: $rightResult->getFalseyScope(),
			typeCallback: static function (bool $nativeTypesPromoted) use ($leftResult, $rightResult): Type {
				$leftBooleanType = ($nativeTypesPromoted ? $leftResult->getNativeType() : $leftResult->getType())->toBoolean();
				if ($leftBooleanType->isTrue()->yes()) {
					return new ConstantBooleanType(true);
				}

				// the right side was processed on the left-falsey scope including
				// the left's side effects (assignments, by-ref writes) - that
				// captured scope is the evaluation point, no re-walk and no
				// depth cap needed
				$rightBooleanType = ($nativeTypesPromoted ? $rightResult->getNativeType() : $rightResult->getType())->toBoolean();
				if ($rightBooleanType->isTrue()->yes()) {
					return new ConstantBooleanType(true);
				}

				if (
					$leftBooleanType->isFalse()->yes()
					&& $rightBooleanType->isFalse()->yes()
				) {
					return new ConstantBooleanType(false);
				}

				return new BooleanType();
			},
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr, $leftResult, $rightResult, $nodeScopeResolver): SpecifiedTypes {
				$leftTypes = $leftResult->getSpecifiedTypesForScope($s, $context)->setRootExpr($expr);
				$rightScope = $leftResult->getFalseyScope();
				$rightTypes = $rightResult->getSpecifiedTypesForScope($rightScope, $context)->setRootExpr($expr);

				if ($context->true()) {
					if (
						$leftResult->getTypeForScope($s)->toBoolean()->isFalse()->yes()
					) {
						$types = $rightTypes->normalize($rightScope, $nodeScopeResolver);
					} elseif (
						$leftResult->getTypeForScope($s)->toBoolean()->isTrue()->yes()
						|| $rightResult->getTypeForScope($s)->toBoolean()->isFalse()->yes()
					) {
						$types = $leftTypes->normalize($s, $nodeScopeResolver);
					} else {
						$leftNormalized = $leftTypes->normalize($s, $nodeScopeResolver);
						$rightNormalized = $rightTypes->normalize($rightScope, $nodeScopeResolver);
						$types = $leftNormalized->intersectWith($rightNormalized);
						$types = $this->augmentBooleanOrTruthyWithConditionalHolders(
							$nodeScopeResolver,
							$s,
							$leftResult->getTruthyScope(),
							$rightScope,
							$rightResult->getTruthyScope(),
							$expr,
							$types);
						$types = $this->conditionalExpressionHolderHelper->augmentDisjunctionTypes($nodeScopeResolver, $s, $leftNormalized, $rightNormalized, $leftResult->getTruthyScope(), $rightResult->getTruthyScope(), $types);
					}
				} else {
					$types = $leftTypes->unionWith($rightTypes);
				}

				if ($context->true()) {
					$result = new SpecifiedTypes(
						$types->getSureTypes(),
						$types->getSureNotTypes(),
					);
					if ($types->shouldOverwrite()) {
						$result = $result->setAlwaysOverwriteTypes();
					}
					return $result->setNewConditionalExpressionHolders($this->conditionalExpressionHolderHelper->mergeConditionalHolders([
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $leftTypes, $rightTypes, false, false, $rightScope, $expr->right),
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $rightTypes, $leftTypes, false, false, $s, $expr->left),
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $leftTypes, $rightTypes, true, false, $rightScope, $expr->right),
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $rightTypes, $leftTypes, true, false, $s, $expr->left),
					]))->setRootExpr($expr);
				}

				return $types;
			},
		);
	}

}
