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
use PHPStan\Analyser\ExprHandler\Helper\BooleanNarrowingHelper;
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

/**
 * @implements ExprHandler<BooleanAnd|LogicalAnd>
 */
#[AutowiredService]
final class BooleanAndHandler implements ExprHandler
{

	public function __construct(
		private BooleanNarrowingHelper $booleanNarrowingHelper,
		private ExpressionResultFactory $expressionResultFactory,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof BooleanAnd || $expr instanceof LogicalAnd;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$leftResult = $nodeScopeResolver->processExprNode($stmt, $expr->left, $scope, $storage, $nodeCallback, $context->enterDeep());
		$leftTruthyScope = $leftResult->getTruthyScope();
		$rightResult = $nodeScopeResolver->processExprNode($stmt, $expr->right, $leftTruthyScope, $storage, $nodeCallback, $context);
		$rightExprType = $rightResult->getType();
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
			specifyTypesCallback: function (TypeSpecifierContext $context, bool $nativeTypesPromoted) use ($expr, $leftResult, $rightResult, $nodeScopeResolver, $scope): SpecifiedTypes {
				return $this->booleanNarrowingHelper->specifyConjunction(
					$nodeScopeResolver,
					$nativeTypesPromoted ? $scope->doNotTreatPhpDocTypesAsCertain() : $scope,
					$context,
					$expr,
					$expr->left,
					static fn (MutatingScope $scope, TypeSpecifierContext $ctx): SpecifiedTypes => $leftResult->getSpecifiedTypesForScope($scope, $ctx),
					$leftResult->getTruthyScope(),
					$leftResult->getFalseyScope(),
					$expr->right,
					static fn (MutatingScope $scope, TypeSpecifierContext $ctx): SpecifiedTypes => $rightResult->getSpecifiedTypesForScope($scope, $ctx),
					$rightResult->getFalseyScope(),
				);
			},
		);
	}

}
