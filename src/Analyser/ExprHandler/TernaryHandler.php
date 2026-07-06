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
use PHPStan\Analyser\ExprHandler\Helper\BooleanNarrowingHelper;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Type\BooleanType;
use PHPStan\Type\Constant\ConstantBooleanType;
use PHPStan\Type\NeverType;
use PHPStan\Type\Type;
use WeakMap;
use PHPStan\Type\TypeCombinator;
use function array_merge;

/**
 * @implements ExprHandler<Ternary>
 */
#[AutowiredService]
final class TernaryHandler implements ExprHandler
{

	/** @var WeakMap<Ternary, array{ExpressionResult, ExpressionResult, ExpressionResult}> */
	private WeakMap $capturedResults;

	public function __construct(
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
		private BooleanNarrowingHelper $booleanNarrowingHelper,
	)
	{
		$this->capturedResults = new WeakMap();
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof Ternary;
	}

	/**
	 * The cond/if/else results captured during the walk, for the assign-time
	 * conditional holders - null for short ternaries and unwalked nodes.
	 *
	 * @return array{ExpressionResult, ExpressionResult, ExpressionResult}|null
	 */
	public function getCapturedResults(Ternary $expr): ?array
	{
		return $this->capturedResults[$expr] ?? null;
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
			$ifTrueType = $ifResult->getType();

			$elseResult = $nodeScopeResolver->processExprNode($stmt, $expr->else, $ifFalseScope, $storage, $nodeCallback, $context);
			$throwPoints = array_merge($throwPoints, $elseResult->getThrowPoints());
			$impurePoints = array_merge($impurePoints, $elseResult->getImpurePoints());
			$hasYield = $hasYield || $elseResult->hasYield();
			$ifFalseScope = $elseResult->getScope();
		}

		if ($ifResult !== null) {
			$this->capturedResults[$expr] = [$ternaryCondResult, $ifResult, $elseResult];
		}

		$condType = $ternaryCondResult->getType();
		if ($condType->isTrue()->yes()) {
			$finalScope = $ifTrueScope;
		} elseif ($condType->isFalse()->yes()) {
			$finalScope = $ifFalseScope;
		} else {
			if ($ifTrueType instanceof NeverType && $ifTrueType->isExplicit()) {
				$finalScope = $ifFalseScope;
			} else {
				$ifFalseType = $elseResult->getType();

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
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr, $ternaryCondResult, $ifResult, $elseResult, $nodeScopeResolver): SpecifiedTypes {
				if ($expr->cond instanceof Ternary || $context->null()) {
					return $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
				}

				// cond ? if : else narrows like (cond && if) || (!cond && else),
				// composed from the walk's results through the boolean helpers -
				// the fabricated nodes are only printed into holder keys
				$notCondNode = new Expr\BooleanNot($expr->cond);

				$condTypes = static fn (MutatingScope $scope, TypeSpecifierContext $ctx): SpecifiedTypes => $ternaryCondResult->getSpecifiedTypesForScope($scope, $ctx);
				$condType = static fn (bool $nativeTypesPromoted): Type => $nativeTypesPromoted ? $ternaryCondResult->getNativeType() : $ternaryCondResult->getType();
				$notCondTypes = static fn (MutatingScope $scope, TypeSpecifierContext $ctx): SpecifiedTypes => $ternaryCondResult->getSpecifiedTypesForScope($scope, $ctx->negate());
				$notCondType = static function (bool $nativeTypesPromoted) use ($ternaryCondResult): Type {
					$bool = ($nativeTypesPromoted ? $ternaryCondResult->getNativeType() : $ternaryCondResult->getType())->toBoolean();
					if ($bool->isTrue()->yes()) {
						return new ConstantBooleanType(false);
					}
					if ($bool->isFalse()->yes()) {
						return new ConstantBooleanType(true);
					}

					return new BooleanType();
				};
				$andVerdict = static function (callable $left, callable $right): callable {
					return static function (bool $nativeTypesPromoted) use ($left, $right): Type {
						$leftBool = $left($nativeTypesPromoted)->toBoolean();
						$rightBool = $right($nativeTypesPromoted)->toBoolean();
						if ($leftBool->isFalse()->yes() || $rightBool->isFalse()->yes()) {
							return new ConstantBooleanType(false);
						}
						if ($leftBool->isTrue()->yes() && $rightBool->isTrue()->yes()) {
							return new ConstantBooleanType(true);
						}

						return new BooleanType();
					};
				};
				$elseTypes = static fn (MutatingScope $scope, TypeSpecifierContext $ctx): SpecifiedTypes => $elseResult->getSpecifiedTypesForScope($scope, $ctx);
				$elseType = static fn (bool $nativeTypesPromoted): Type => $nativeTypesPromoted ? $elseResult->getNativeType() : $elseResult->getType();

				$condTruthyScope = $s->applySpecifiedTypes($condTypes($s, TypeSpecifierContext::createTruthy()));
				$condFalseyScope = $s->applySpecifiedTypes($condTypes($s, TypeSpecifierContext::createFalsey()));

				// right disjunct: !cond && else
				$bNode = new BooleanAnd($notCondNode, $expr->else);
				$elseFalseyOnCondFalseyScope = $condFalseyScope->applySpecifiedTypes($elseTypes($condFalseyScope, TypeSpecifierContext::createFalsey()));
				$bTypes = fn (MutatingScope $scope, TypeSpecifierContext $ctx): SpecifiedTypes => $this->booleanNarrowingHelper->specifyConjunction(
					$nodeScopeResolver,
					$scope,
					$ctx,
					$bNode,
					$notCondNode,
					$notCondTypes,
					$condFalseyScope,
					$condTruthyScope,
					$expr->else,
					$elseTypes,
					$elseFalseyOnCondFalseyScope,
				);
				$bType = $andVerdict($notCondType, $elseType);
				$bTruthyScope = $s->applySpecifiedTypes($bTypes($s, TypeSpecifierContext::createTruthy()));

				if ($ifResult !== null && $expr->if !== null) {
					// left disjunct: cond && if
					$aNode = new BooleanAnd($expr->cond, $expr->if);
					$ifTypes = static fn (MutatingScope $scope, TypeSpecifierContext $ctx): SpecifiedTypes => $ifResult->getSpecifiedTypesForScope($scope, $ctx);
					$ifType = static fn (bool $nativeTypesPromoted): Type => $nativeTypesPromoted ? $ifResult->getNativeType() : $ifResult->getType();
					$ifFalseyOnCondTruthyScope = $condTruthyScope->applySpecifiedTypes($ifTypes($condTruthyScope, TypeSpecifierContext::createFalsey()));
					$aTypes = fn (MutatingScope $scope, TypeSpecifierContext $ctx): SpecifiedTypes => $this->booleanNarrowingHelper->specifyConjunction(
						$nodeScopeResolver,
						$scope,
						$ctx,
						$aNode,
						$expr->cond,
						$condTypes,
						$condTruthyScope,
						$condFalseyScope,
						$expr->if,
						$ifTypes,
						$ifFalseyOnCondTruthyScope,
					);
					$aType = $andVerdict($condType, $ifType);
					$aTruthyScope = $s->applySpecifiedTypes($aTypes($s, TypeSpecifierContext::createTruthy()));
					$aFalseyScope = $s->applySpecifiedTypes($aTypes($s, TypeSpecifierContext::createFalsey()));

					return $this->booleanNarrowingHelper->specifyDisjunction(
						$nodeScopeResolver,
						$s,
						$context,
						$expr,
						$aNode,
						$aTypes,
						$aType,
						$aTruthyScope,
						$aFalseyScope,
						$bNode,
						$bTypes,
						$bType,
						$bTruthyScope,
					)->setRootExpr($expr);
				}

				// short ternary: cond || (!cond && else)
				return $this->booleanNarrowingHelper->specifyDisjunction(
					$nodeScopeResolver,
					$s,
					$context,
					$expr,
					$expr->cond,
					$condTypes,
					$condType,
					$condTruthyScope,
					$condFalseyScope,
					$bNode,
					$bTypes,
					$bType,
					$bTruthyScope,
				)->setRootExpr($expr);
			},
		);
	}

}
