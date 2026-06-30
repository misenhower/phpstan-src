<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\Equal;
use PhpParser\Node\Expr\BinaryOp\NotEqual;
use PhpParser\Node\Expr\Cast;
use PhpParser\Node\Expr\ConstFetch;
use PhpParser\Node\Name\FullyQualified;
use PhpParser\Node\Scalar\Float_;
use PhpParser\Node\Scalar\Int_;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Reflection\InitializerExprTypeResolver;
use PHPStan\ShouldNotHappenException;
use PHPStan\Type\NullType;
use PHPStan\Type\Type;

/**
 * @implements ExprHandler<Cast>
 */
#[AutowiredService]
final class CastHandler implements ExprHandler
{

	public function __construct(
		private InitializerExprTypeResolver $initializerExprTypeResolver,
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof Cast && !$expr instanceof Cast\String_;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		$exprResult = $nodeScopeResolver->processExprNode($stmt, $expr->expr, $scope, $storage, $nodeCallback, $context->enterDeep());
		$scope = $exprResult->getScope();

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $exprResult->hasYield(),
			isAlwaysTerminating: $exprResult->isAlwaysTerminating(),
			throwPoints: $exprResult->getThrowPoints(),
			impurePoints: $exprResult->getImpurePoints(),
			typeCallback: function (bool $nativeTypesPromoted) use ($expr, $exprResult): Type {
				if ($expr instanceof Cast\Unset_) {
					return new NullType();
				}

				return $this->initializerExprTypeResolver->getCastType($expr, static function (Expr $e) use ($nativeTypesPromoted, $expr, $exprResult): Type {
					if ($e === $expr->expr) {
						return $nativeTypesPromoted ? $exprResult->getNativeType() : $exprResult->getType();
					}

					throw new ShouldNotHappenException();
				});
			},
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr): SpecifiedTypes {
				if ($expr instanceof Cast\Bool_) {
					return $s->obtainResultForNode(new Equal($expr->expr, new ConstFetch(new FullyQualified('true'))))->getSpecifiedTypesForScope($s, $context)->setRootExpr($expr);
				}

				if ($expr instanceof Cast\Int_) {
					return $s->obtainResultForNode(new NotEqual($expr->expr, new Int_(0)))->getSpecifiedTypesForScope($s, $context)->setRootExpr($expr);
				}

				if ($expr instanceof Cast\Double) {
					return $s->obtainResultForNode(new NotEqual($expr->expr, new Float_(0.0)))->getSpecifiedTypesForScope($s, $context)->setRootExpr($expr);
				}

				return $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
			},
		);
	}

}
