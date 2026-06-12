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
	private function augmentBooleanOrTruthyWithConditionalHolders(MutatingScope $scope, MutatingScope $rightScope, BooleanOr|LogicalOr $expr, SpecifiedTypes $types): SpecifiedTypes
	{
		$leftTruthyScope = $scope->filterByTruthyValue($expr->left);
		$rightTruthyScope = $rightScope->filterByTruthyValue($expr->right);

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

				$origType = $scope->getType($targetExpr);
				$leftType = $leftTruthyScope->getType($targetExpr);
				$rightType = $rightTruthyScope->getType($targetExpr);

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
		$rightExprType = $rightResult->getScope()->getType($expr->right);
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
			truthyScopeCallback: static fn (): MutatingScope => $leftMergedWithRightScope->filterByTruthyValue($expr),
			falseyScopeCallback: static fn (): MutatingScope => $rightResult->getScope()->filterByFalseyValue($expr->right),
			typeCallback: static function (MutatingScope $s) use ($leftResult, $rightResult, $leftFalseyScope): Type {
				$leftBooleanType = $leftResult->getTypeForScope($s)->toBoolean();
				if ($leftBooleanType->isTrue()->yes()) {
					return new ConstantBooleanType(true);
				}

				// the right side was processed on the left-falsey scope including
				// the left's side effects (assignments, by-ref writes) - that
				// captured scope is the evaluation point, no re-walk and no
				// depth cap needed
				$rightBooleanType = $rightResult->getTypeForScope($s->nativeTypesPromoted ? $leftFalseyScope->doNotTreatPhpDocTypesAsCertain() : $leftFalseyScope)->toBoolean();
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
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr, $leftResult, $rightResult): SpecifiedTypes {
				$leftTypes = $this->defaultNarrowingHelper->getChildSpecifiedTypes($s, $expr->left, $leftResult, $context)->setRootExpr($expr);
				$rightScope = $s->filterByFalseyValue($expr->left);
				$rightTypes = $this->defaultNarrowingHelper->getChildSpecifiedTypes($rightScope, $expr->right, $rightResult, $context)->setRootExpr($expr);

				if ($context->true()) {
					if (
						$leftResult->getTypeForScope($s)->toBoolean()->isFalse()->yes()
					) {
						$types = $rightTypes->normalize($rightScope);
					} elseif (
						$leftResult->getTypeForScope($s)->toBoolean()->isTrue()->yes()
						|| $rightResult->getTypeForScope($s)->toBoolean()->isFalse()->yes()
					) {
						$types = $leftTypes->normalize($s);
					} else {
						$leftNormalized = $leftTypes->normalize($s);
						$rightNormalized = $rightTypes->normalize($rightScope);
						$types = $leftNormalized->intersectWith($rightNormalized);
						$types = $this->augmentBooleanOrTruthyWithConditionalHolders($s, $rightScope, $expr, $types);
						$types = $this->conditionalExpressionHolderHelper->augmentDisjunctionTypes($s, $rightScope, $leftNormalized, $rightNormalized, $expr->left, $expr->right, true, $types);
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
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($s, $leftTypes, $rightTypes, false, false, $rightScope, $expr->right),
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($s, $rightTypes, $leftTypes, false, false, $s, $expr->left),
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($s, $leftTypes, $rightTypes, true, false, $rightScope, $expr->right),
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($s, $rightTypes, $leftTypes, true, false, $s, $expr->left),
					]))->setRootExpr($expr);
				}

				return $types;
			},
		);
	}

}
