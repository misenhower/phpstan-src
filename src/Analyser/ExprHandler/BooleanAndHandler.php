<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\BooleanAnd;
use PhpParser\Node\Expr\BinaryOp\LogicalAnd;
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
use PHPStan\Node\BooleanAndNode;
use PHPStan\Type\BooleanType;
use PHPStan\Type\Constant\ConstantBooleanType;
use PHPStan\Type\NeverType;
use PHPStan\Type\Type;
use function array_merge;
use function is_string;

/**
 * @implements ExprHandler<BooleanAnd|LogicalAnd>
 */
#[AutowiredService]
final class BooleanAndHandler implements ExprHandler
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
		return $expr instanceof BooleanAnd || $expr instanceof LogicalAnd;
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

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$leftResult = $nodeScopeResolver->processExprNode($stmt, $expr->left, $scope, $storage, $nodeCallback, $context->enterDeep());
		$leftTruthyScope = $leftResult->getTruthyScope();
		$rightResult = $nodeScopeResolver->processExprNode($stmt, $expr->right, $leftTruthyScope, $storage, $nodeCallback, $context);
		$rightExprType = $rightResult->getTypeForScope($rightResult->getScope());
		if ($rightExprType instanceof NeverType && $rightExprType->isExplicit()) {
			$leftMergedWithRightScope = $leftResult->getFalseyScope();
		} else {
			$leftMergedWithRightScope = $leftResult->getScope()->mergeWith($rightResult->getScope());
		}

		$nodeScopeResolver->callNodeCallbackWithExpression($nodeCallback, new BooleanAndNode($expr, $leftTruthyScope), $scope, $storage, $context);

		return $this->expressionResultFactory->create(
			$leftMergedWithRightScope,
			beforeScope: $scope,
			expr: $expr,
			hasYield: $leftResult->hasYield() || $rightResult->hasYield(),
			isAlwaysTerminating: $leftResult->isAlwaysTerminating(),
			throwPoints: array_merge($leftResult->getThrowPoints(), $rightResult->getThrowPoints()),
			impurePoints: array_merge($leftResult->getImpurePoints(), $rightResult->getImpurePoints()),
			// && is truthy only when the right side was evaluated (on the left-truthy
			// scope) and is itself truthy - that is exactly the right operand's truthy
			// scope: it carries the left narrowing and the right's by-ref/side-effect
			// definitions, and does not re-apply the left narrowing over a variable the
			// right operand reassigned (bug-9400).
			truthyScopeOverride: $rightResult->getTruthyScope(),
			typeCallback: static function (bool $nativeTypesPromoted) use ($leftResult, $rightResult): Type {
				$leftBooleanType = ($nativeTypesPromoted ? $leftResult->getNativeType() : $leftResult->getType())->toBoolean();
				if ($leftBooleanType->isFalse()->yes()) {
					return new ConstantBooleanType(false);
				}

				// the right side was processed on the left-truthy scope including
				// the left's side effects (assignments, by-ref writes) - that
				// captured scope is the evaluation point, no re-walk and no
				// depth cap needed
				$rightBooleanType = ($nativeTypesPromoted ? $rightResult->getNativeType() : $rightResult->getType())->toBoolean();
				if ($rightBooleanType->isFalse()->yes()) {
					return new ConstantBooleanType(false);
				}

				if (
					$leftBooleanType->isTrue()->yes()
					&& $rightBooleanType->isTrue()->yes()
				) {
					return new ConstantBooleanType(true);
				}

				return new BooleanType();
			},
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr, $leftResult, $rightResult, $nodeScopeResolver): SpecifiedTypes {
				$leftTypes = $this->defaultNarrowingHelper->getChildSpecifiedTypes($s, $expr->left, $leftResult, $context)->setRootExpr($expr);
				$rightScope = $leftResult->getTruthyScope();
				$rightTypes = $this->defaultNarrowingHelper->getChildSpecifiedTypes($rightScope, $expr->right, $rightResult, $context)->setRootExpr($expr);
				if ($context->true()) {
					$types = $leftTypes->unionWith($rightTypes);
				} else {
					$leftNormalized = $leftTypes->normalize($s, $nodeScopeResolver);
					$rightNormalized = $rightTypes->normalize($rightScope, $nodeScopeResolver);
					$types = $leftNormalized->intersectWith($rightNormalized);
					$types = $this->conditionalExpressionHolderHelper->augmentDisjunctionTypes($nodeScopeResolver, $s, $leftNormalized, $rightNormalized, $leftResult->getFalseyScope(), $rightResult->getFalseyScope(), $types);
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
							$leftHolderTypes = $this->defaultNarrowingHelper->getChildSpecifiedTypes($s, $expr->left, $leftResult, TypeSpecifierContext::createFalsey())->setRootExpr($expr);
						}
						if ($rightHolderTypes->getSureTypes() === [] && $rightHolderTypes->getSureNotTypes() === []) {
							$rightHolderTypes = $this->defaultNarrowingHelper->getChildSpecifiedTypes($rightScope, $expr->right, $rightResult, TypeSpecifierContext::createFalsey())->setRootExpr($expr);
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
						$truthyLeftTypes = $this->defaultNarrowingHelper->getChildSpecifiedTypes($s, $expr->left, $leftResult, TypeSpecifierContext::createTruthy());
						if ($this->allExpressionsTrackable($truthyLeftTypes)) {
							$leftCondTypes = new SpecifiedTypes($truthyLeftTypes->getSureNotTypes(), $truthyLeftTypes->getSureTypes());
						}
					}
					if ($rightCondTypes->getSureTypes() === [] && $rightCondTypes->getSureNotTypes() === []) {
						$truthyRightTypes = $this->defaultNarrowingHelper->getChildSpecifiedTypes($rightScope, $expr->right, $rightResult, TypeSpecifierContext::createTruthy());
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
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $leftCondTypes, $rightHolderTypes, false, true, $rightScope, $expr->right),
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $rightCondTypes, $leftHolderTypes, false, true, $s, $expr->left),
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $leftCondTypes, $rightHolderTypes, true, true, $rightScope, $expr->right),
						$this->conditionalExpressionHolderHelper->processBooleanConditionalTypes($nodeScopeResolver, $s, $rightCondTypes, $leftHolderTypes, true, true, $s, $expr->left),
					]))->setRootExpr($expr);
				}

				return $types;
			},
		);
	}

}
