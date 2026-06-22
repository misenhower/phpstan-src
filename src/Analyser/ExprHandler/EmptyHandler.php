<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\BooleanOr;
use PhpParser\Node\Expr\Empty_;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\NonNullabilityHelper;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifier;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\EmptyExpressionNode;
use PHPStan\Type\BooleanType;
use PHPStan\Type\Constant\ConstantBooleanType;
use PHPStan\Type\Type;

/**
 * @implements ExprHandler<Empty_>
 */
#[AutowiredService]
final class EmptyHandler implements ExprHandler
{

	public function __construct(
		private NonNullabilityHelper $nonNullabilityHelper,
		private ExpressionResultFactory $expressionResultFactory,
		private TypeSpecifier $typeSpecifier,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof Empty_;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		$nonNullabilityResult = $this->nonNullabilityHelper->ensureNonNullability($nodeScopeResolver, $scope, $expr->expr);
		$scope = $nodeScopeResolver->lookForSetAllowedUndefinedExpressions($nonNullabilityResult->getScope(), $expr->expr);
		$exprResult = $nodeScopeResolver->processExprNode($stmt, $expr->expr, $scope, $storage, $nodeCallback, $context->enterDeep());
		$scope = $exprResult->getScope();
		$scope = $this->nonNullabilityHelper->revertNonNullability($scope, $nonNullabilityResult->getSpecifiedExpressions());
		$scope = $nodeScopeResolver->lookForUnsetAllowedUndefinedExpressions($scope, $expr->expr);

		$nodeScopeResolver->callNodeCallbackWithExpression($nodeCallback, new EmptyExpressionNode($expr, $exprResult), $beforeScope, $storage, $context);

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $exprResult->hasYield(),
			isAlwaysTerminating: $exprResult->isAlwaysTerminating(),
			throwPoints: $exprResult->getThrowPoints(),
			impurePoints: $exprResult->getImpurePoints(),
			typeCallback: static function (MutatingScope $s) use ($exprResult): Type {
				$result = $exprResult->getIssetabilityResolution($s, false)->notEmpty();
				if ($result === null) {
					return new BooleanType();
				}

				return new ConstantBooleanType(!$result);
			},
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr, $exprResult): SpecifiedTypes {
				$isset = $exprResult->getIssetabilityResolution($s, false)->isSet(static fn (): bool => true);
				if ($isset === false) {
					return new SpecifiedTypes();
				}

				return $this->typeSpecifier->specifyTypesInCondition($s, new BooleanOr(
					new Expr\BooleanNot(new Expr\Isset_([$expr->expr])),
					new Expr\BooleanNot($expr->expr),
				), $context)->setRootExpr($expr);
			},
		);
	}

}
