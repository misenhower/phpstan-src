<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Virtual;

use PhpParser\Node\Expr;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Expr\SetOffsetValueTypeExpr;
use PHPStan\Type\Type;

/**
 * @implements ExprHandler<SetOffsetValueTypeExpr>
 */
#[AutowiredService]
final class SetOffsetValueTypeExprHandler implements ExprHandler
{

	public function __construct(private ExpressionResultFactory $expressionResultFactory)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof SetOffsetValueTypeExpr;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		// virtual node: callers only read the type, computed lazily by the
		// typeCallback. A null specifyTypesCallback falls back to default
		// narrowing in TypeSpecifier, matching the old specifyDefaultTypes().
		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $scope,
			expr: $expr,
			hasYield: false,
			isAlwaysTerminating: false,
			throwPoints: [],
			impurePoints: [],
			typeCallback: static fn (MutatingScope $s): Type => $s->getType($expr->getVar())->setOffsetValueType(
				$expr->getDim() !== null ? $s->getType($expr->getDim()) : null,
				$s->getType($expr->getValue()),
			),
		);
	}

}
