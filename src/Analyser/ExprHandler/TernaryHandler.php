<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\BooleanAnd;
use PhpParser\Node\Expr\BinaryOp\BooleanOr;
use PhpParser\Node\Expr\Ternary;
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
use PHPStan\Type\NeverType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use function array_merge;

/**
 * @implements ExprHandler<Ternary>
 */
#[AutowiredService]
final class TernaryHandler implements ExprHandler
{

	public function __construct(
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof Ternary;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$ternaryCondResult = $nodeScopeResolver->processExprNode($stmt, $expr->cond, $scope, $storage, $nodeCallback, $context->enterDeep());
		$throwPoints = $ternaryCondResult->getThrowPoints();
		$impurePoints = $ternaryCondResult->getImpurePoints();
		$hasYield = $ternaryCondResult->hasYield();
		$ifTrueScope = $ternaryCondResult->getTruthyScope();
		$ifFalseScope = $ternaryCondResult->getFalseyScope();
		$ifTrueType = null;
		$ifResult = null;

		$ifProcessingScope = $ifTrueScope;
		$elseProcessingScope = $ifFalseScope;
		if ($expr->if === null) {
			$elseResult = $nodeScopeResolver->processExprNode($stmt, $expr->else, $ifFalseScope, $storage, $nodeCallback, $context);
			$throwPoints = array_merge($throwPoints, $elseResult->getThrowPoints());
			$impurePoints = array_merge($impurePoints, $elseResult->getImpurePoints());
			$hasYield = $hasYield || $elseResult->hasYield();
			$ifFalseScope = $elseResult->getScope();
		} else {
			$ifResult = $nodeScopeResolver->processExprNode($stmt, $expr->if, $ifTrueScope, $storage, $nodeCallback, $context);
			$throwPoints = array_merge($throwPoints, $ifResult->getThrowPoints());
			$impurePoints = array_merge($impurePoints, $ifResult->getImpurePoints());
			$hasYield = $hasYield || $ifResult->hasYield();
			$ifTrueScope = $ifResult->getScope();
			$ifTrueType = $ifResult->getTypeForScope($ifTrueScope);

			$elseResult = $nodeScopeResolver->processExprNode($stmt, $expr->else, $ifFalseScope, $storage, $nodeCallback, $context);
			$throwPoints = array_merge($throwPoints, $elseResult->getThrowPoints());
			$impurePoints = array_merge($impurePoints, $elseResult->getImpurePoints());
			$hasYield = $hasYield || $elseResult->hasYield();
			$ifFalseScope = $elseResult->getScope();
		}

		$condType = $ternaryCondResult->getTypeForScope($scope);
		if ($condType->isTrue()->yes()) {
			$finalScope = $ifTrueScope;
		} elseif ($condType->isFalse()->yes()) {
			$finalScope = $ifFalseScope;
		} else {
			if ($ifTrueType instanceof NeverType && $ifTrueType->isExplicit()) {
				$finalScope = $ifFalseScope;
			} else {
				$ifFalseType = $elseResult->getTypeForScope($ifFalseScope);

				if ($ifFalseType instanceof NeverType && $ifFalseType->isExplicit()) {
					$finalScope = $ifTrueScope;
				} else {
					$finalScope = $ifTrueScope->mergeWith($ifFalseScope);
				}
			}
		}

		return $this->expressionResultFactory->create(
			$finalScope,
			beforeScope: $scope,
			expr: $expr,
			hasYield: $hasYield,
			isAlwaysTerminating: $ternaryCondResult->isAlwaysTerminating(),
			throwPoints: $throwPoints,
			impurePoints: $impurePoints,
			// the branches were processed on the cond-truthy/cond-falsey scopes
			// including the condition's side effects - those captured scopes
			// are the evaluation points, no re-walk needed
			typeCallback: static function (bool $nativeTypesPromoted) use ($expr, $ternaryCondResult, $ifResult, $elseResult, $ifProcessingScope, $nodeScopeResolver): Type {
				if ($nativeTypesPromoted) {
					$ifProcessingScope = $ifProcessingScope->doNotTreatPhpDocTypesAsCertain();
				}
				$booleanConditionType = ($nativeTypesPromoted ? $ternaryCondResult->getNativeType() : $ternaryCondResult->getType())->toBoolean();
				$elseType = ($nativeTypesPromoted ? $elseResult->getNativeType() : $elseResult->getType());
				if ($expr->if === null || $ifResult === null) {
					// short-ternary truthy value: the condition read on its own truthy scope
					// is a different scope than its own, so reprocess it there.
					$condTruthyType = $nodeScopeResolver->processExprOnDemand($expr->cond, $ifProcessingScope, new ExpressionResultStorage())->getType();
					if ($booleanConditionType->isTrue()->yes()) {
						return $condTruthyType;
					}

					if ($booleanConditionType->isFalse()->yes()) {
						return $elseType;
					}

					return TypeCombinator::union(
						TypeCombinator::removeFalsey($condTruthyType),
						$elseType,
					);
				}

				$ifType = ($nativeTypesPromoted ? $ifResult->getNativeType() : $ifResult->getType());
				if ($booleanConditionType->isTrue()->yes()) {
					return $ifType;
				}

				if ($booleanConditionType->isFalse()->yes()) {
					return $elseType;
				}

				return TypeCombinator::union(
					$ifType,
					$elseType,
				);
			},
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr): SpecifiedTypes {
				if ($expr->cond instanceof Ternary || $context->null()) {
					return $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
				}

				if ($expr->if !== null) {
					$conditionExpr = new BooleanOr(
						new BooleanAnd($expr->cond, $expr->if),
						new BooleanAnd(new Expr\BooleanNot($expr->cond), $expr->else),
					);
				} else {
					$conditionExpr = new BooleanOr(
						$expr->cond,
						new BooleanAnd(new Expr\BooleanNot($expr->cond), $expr->else),
					);
				}

				// the synthetic condition takes the on-demand bridge; its real
				// subnodes answer from stored results
				return $this->defaultNarrowingHelper->getChildSpecifiedTypes($s, $conditionExpr, null, $context)->setRootExpr($expr);
			},
		);
	}

}
