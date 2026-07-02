<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\Coalesce;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\ExprHandler\Helper\NonNullabilityHelper;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\CoalesceExpressionNode;
use PHPStan\Type\Constant\ConstantBooleanType;
use PHPStan\Type\NeverType;
use PHPStan\Type\NullType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use function array_merge;

/**
 * @implements ExprHandler<Coalesce>
 */
#[AutowiredService]
final class CoalesceHandler implements ExprHandler
{

	public function __construct(
		private NonNullabilityHelper $nonNullabilityHelper,
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof Coalesce;
	}

	/**
	 * A falsey coalesce means its left side was null (when it was surely set) -
	 * shared by the specifyTypesCallback and by processExpr() for the scope
	 * the right side evaluates under.
	 *
	 * @param Coalesce $expr
	 */
	private function getFalseySpecifiedTypes(MutatingScope $s, Expr $expr, ExpressionResult $condResult, TypeSpecifierContext $context): SpecifiedTypes
	{
		$isset = $condResult->getIssetabilityResolution($s, false)->isSet(static fn (): bool => true);

		if ($isset !== true) {
			return new SpecifiedTypes();
		}

		return $this->defaultNarrowingHelper->createSubjectTypes($s, $expr->left, $condResult, new NullType(), $context->negate())->setRootExpr($expr);
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		$nonNullabilityResult = $this->nonNullabilityHelper->ensureNonNullability($nodeScopeResolver, $scope, $expr->left);
		$condScope = $nodeScopeResolver->lookForSetAllowedUndefinedExpressions($nonNullabilityResult->getScope(), $expr->left);
		$condResult = $nodeScopeResolver->processExprNode($stmt, $expr->left, $condScope, $storage, $nodeCallback, $context->enterDeep());
		$scope = $this->nonNullabilityHelper->revertNonNullability($condResult->getScope(), $nonNullabilityResult->getSpecifiedExpressions());
		$scope = $nodeScopeResolver->lookForUnsetAllowedUndefinedExpressions($scope, $expr->left);

		// the falsey narrowing of this very node - asking the scope about it
		// mid-processing would take the on-demand path and recurse
		$rightScope = $scope->applySpecifiedTypes($this->getFalseySpecifiedTypes($scope, $expr, $condResult, TypeSpecifierContext::createFalsey()));
		$rightResult = $nodeScopeResolver->processExprNode($stmt, $expr->right, $rightScope, $storage, $nodeCallback, $context->enterDeep());
		$rightExprType = $rightResult->getType();
		if ($rightExprType instanceof NeverType && $rightExprType->isExplicit()) {
			$scope = $scope->applySpecifiedTypes($nodeScopeResolver->processExprOnDemand(new Expr\Isset_([$expr->left]), $scope, new ExpressionResultStorage())->getSpecifiedTypesForScope($scope, TypeSpecifierContext::createTruthy()));
		} else {
			$scope = $scope->applySpecifiedTypes($nodeScopeResolver->processExprOnDemand(new Expr\Isset_([$expr->left]), $scope, new ExpressionResultStorage())->getSpecifiedTypesForScope($scope, TypeSpecifierContext::createTruthy()))->mergeWith($rightResult->getScope());
		}

		$nodeScopeResolver->callNodeCallbackWithExpression($nodeCallback, new CoalesceExpressionNode($expr, $condResult, 'on left side of ??'), $beforeScope, $storage, $context);

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $condResult->hasYield() || $rightResult->hasYield(),
			isAlwaysTerminating: $condResult->isAlwaysTerminating(),
			throwPoints: array_merge($condResult->getThrowPoints(), $rightResult->getThrowPoints()),
			impurePoints: array_merge($condResult->getImpurePoints(), $rightResult->getImpurePoints()),
			typeCallback: static function (bool $nativeTypesPromoted) use ($expr, $condResult, $rightResult, $nodeScopeResolver, $beforeScope): Type {
				$issetLeftExpr = new Expr\Isset_([$expr->left]);

				// the isset resolution and the left-is-set narrowing run on
				// beforeScope (the evaluation point), not the asking scope.
				$result = $condResult->getIssetabilityResolution($beforeScope, false)->isSet(static function (Type $type): ?bool {
					$isNull = $type->isNull();
					if ($isNull->maybe()) {
						return null;
					}

					return !$isNull->yes();
				});

				if ($result !== null && $result !== false) {
					return TypeCombinator::removeNull($nodeScopeResolver->processExprOnDemand($expr->left, $beforeScope->applySpecifiedTypes($nodeScopeResolver->processExprOnDemand($issetLeftExpr, $beforeScope, new ExpressionResultStorage())->getSpecifiedTypesForScope($beforeScope, TypeSpecifierContext::createTruthy())), new ExpressionResultStorage())->getType());
				}

				// the right side was processed on the left-is-null scope, so its own
				// result is the evaluation point.
				$rightType = $nativeTypesPromoted ? $rightResult->getNativeType() : $rightResult->getType();

				if ($result === null) {
					return TypeCombinator::union(
						TypeCombinator::removeNull($nodeScopeResolver->processExprOnDemand($expr->left, $beforeScope->applySpecifiedTypes($nodeScopeResolver->processExprOnDemand($issetLeftExpr, $beforeScope, new ExpressionResultStorage())->getSpecifiedTypesForScope($beforeScope, TypeSpecifierContext::createTruthy())), new ExpressionResultStorage())->getType()),
						$rightType,
					);
				}

				return $rightType;
			},
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr, $condResult, $rightResult): SpecifiedTypes {
				if ($context->null()) {
					return $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
				}

				if (!$context->true()) {
					return $this->getFalseySpecifiedTypes($s, $expr, $condResult, $context);
				}

				if ((new ConstantBooleanType(false))->isSuperTypeOf($rightResult->getTypeOnScope($s, $s->nativeTypesPromoted)->toBoolean())->yes()) {
					return $this->defaultNarrowingHelper->createSubjectTypes($s, $expr->left, $condResult, new NullType(), TypeSpecifierContext::createFalse())->setRootExpr($expr);
				}

				// The Coalesce condition matched but produced no narrowing; the legacy
				// if/elseif chain fell through to its empty-SpecifiedTypes tail here,
				// not to the truthy/falsey default.
				return (new SpecifiedTypes([], []))->setRootExpr($expr);
			},
			// a type constraint on the coalesce constrains its left side when
			// the type rules the right side in or out - what
			// TypeSpecifier::create() recovered by unwrapping the coalesce
			createTypesCallback: function (MutatingScope $s, Type $type, TypeSpecifierContext $context) use ($expr, $condResult, $rightResult): SpecifiedTypes {
				if (!$context->null()) {
					$rightType = $rightResult->getTypeOnScope($s, $s->nativeTypesPromoted);
					if (
						($context->true() && $type->isSuperTypeOf($rightType)->no())
						|| ($context->false() && $type->isSuperTypeOf($rightType)->yes())
					) {
						return $this->defaultNarrowingHelper->createSubjectTypes($s, $expr->left, $condResult, $type, $context);
					}
				}

				return $this->defaultNarrowingHelper->createSubjectTypes($s, $expr, null, $type, $context);
			},
		);
	}

}
