<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use Closure;
use ArrayAccess;
use PhpParser\Node\Expr;
use PhpParser\Node\Expr\ArrayDimFetch;
use PhpParser\Node\Expr\BinaryOp\BooleanAnd;
use PhpParser\Node\Expr\Isset_;
use PhpParser\Node\Expr\MethodCall;
use PhpParser\Node\Expr\PropertyFetch;
use PhpParser\Node\Expr\StaticPropertyFetch;
use PhpParser\Node\Identifier;
use PhpParser\Node\Stmt;
use PhpParser\Node\VarLikeIdentifier;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\BooleanNarrowingHelper;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\ExprHandler\Helper\NonNullabilityHelper;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\NoopNodeCallback;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Expr\TypeExpr;
use PHPStan\Node\IssetExpr;
use PHPStan\Node\IssetExpressionNode;
use PHPStan\Rules\Arrays\AllowedArrayKeysTypes;
use PHPStan\ShouldNotHappenException;
use PHPStan\Type\Accessory\HasOffsetType;
use PHPStan\Type\Accessory\HasPropertyType;
use PHPStan\Type\Accessory\NonEmptyArrayType;
use PHPStan\Type\BooleanType;
use PHPStan\Type\Constant\ConstantBooleanType;
use PHPStan\Type\Constant\ConstantIntegerType;
use PHPStan\Type\Constant\ConstantStringType;
use PHPStan\Type\IntersectionType;
use PHPStan\Type\MixedType;
use PHPStan\Type\NullType;
use PHPStan\Type\ObjectType;
use PHPStan\Type\ObjectWithoutClassType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use function array_merge;
use function array_reverse;
use function array_shift;
use function count;
use function is_string;
use function spl_object_id;

/**
 * @implements ExprHandler<Isset_>
 */
#[AutowiredService]
final class IssetHandler implements ExprHandler
{

	public function __construct(
		private NonNullabilityHelper $nonNullabilityHelper,
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
		private BooleanNarrowingHelper $booleanNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof Isset_;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		$hasYield = false;
		$throwPoints = [];
		$impurePoints = [];
		$nonNullabilityResults = [];
		$isAlwaysTerminating = false;
		$varResults = [];
		foreach ($expr->vars as $var) {
			$nonNullabilityResult = $this->nonNullabilityHelper->ensureNonNullability($nodeScopeResolver, $scope, $var);
			$scope = $nodeScopeResolver->lookForSetAllowedUndefinedExpressions($nonNullabilityResult->getScope(), $var);
			$varResult = $nodeScopeResolver->processExprNode($stmt, $var, $scope, $storage, $nodeCallback, $context->enterDeep());
			$varResults[] = $varResult;
			$scope = $varResult->getScope();
			$hasYield = $hasYield || $varResult->hasYield();
			$throwPoints = array_merge($throwPoints, $varResult->getThrowPoints());
			$impurePoints = array_merge($impurePoints, $varResult->getImpurePoints());
			$isAlwaysTerminating = $isAlwaysTerminating || $varResult->isAlwaysTerminating();
			$nonNullabilityResults[] = $nonNullabilityResult;

			if (!($var instanceof ArrayDimFetch)) {
				continue;
			}

			$varType = $nodeScopeResolver->readStoredResult($var->var, $storage)->getTypeOnScope($scope, false);
			if ($varType->isArray()->yes() || (new ObjectType(ArrayAccess::class))->isSuperTypeOf($varType)->no()) {
				continue;
			}

			$throwPoints = array_merge($throwPoints, $nodeScopeResolver->processExprNode(
				$stmt,
				new MethodCall(new TypeExpr($varType), 'offsetExists'),
				$scope,
				$storage,
				new NoopNodeCallback(),
				$context,
			)->getThrowPoints());
		}
		foreach (array_reverse($expr->vars) as $var) {
			$scope = $nodeScopeResolver->lookForUnsetAllowedUndefinedExpressions($scope, $var);
		}
		foreach (array_reverse($nonNullabilityResults) as $nonNullabilityResult) {
			$scope = $this->nonNullabilityHelper->revertNonNullability($scope, $nonNullabilityResult->getSpecifiedExpressions());
		}

		// The subjects and their chain links were just processed, so their
		// ExpressionResults are in the storage; capture them (the results, not the
		// storage - no reference cycle) so the narrowing reads their types via
		// getTypeOnScope() instead of re-walking through Scope::getType().
		$chainResults = [];
		foreach ($expr->vars as $var) {
			$this->defaultNarrowingHelper->captureChainResults($var, $storage, $chainResults);
		}

		$nodeScopeResolver->callNodeCallbackWithExpression($nodeCallback, new IssetExpressionNode($expr, $varResults), $beforeScope, $storage, $context);

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $hasYield,
			isAlwaysTerminating: $isAlwaysTerminating,
			throwPoints: $throwPoints,
			impurePoints: $impurePoints,
			typeCallback: static function (bool $nativeTypesPromoted) use ($varResults, $beforeScope): Type {
				$issetResult = true;
				foreach ($varResults as $varResult) {
					$result = $varResult->getIssetabilityResolution($nativeTypesPromoted ? $beforeScope->doNotTreatPhpDocTypesAsCertain() : $beforeScope, false)->isSet(static function (Type $type): ?bool {
						$isNull = $type->isNull();
						if ($isNull->maybe()) {
							return null;
						}

						return !$isNull->yes();
					});
					if ($result !== null) {
						if (!$result) {
							return new ConstantBooleanType($result);
						}

						continue;
					}

					$issetResult = $result;
				}

				if ($issetResult === null) {
					return new BooleanType();
				}

				return new ConstantBooleanType($issetResult);
			},
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr, $varResults, $chainResults, $nodeScopeResolver): SpecifiedTypes {
				// type of an already-processed chain link, read from its captured
				// result (re-evaluated on the asking scope, honouring narrowing) -
				// never re-walked through the scope
				$readType = $this->defaultNarrowingHelper->buildChainTypeReader($chainResults, $s, $nodeScopeResolver);

				if (count($expr->vars) === 0 || $context->null()) {
					return $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
				}

				if (count($expr->vars) > 1) {
					// isset($a, $b) is true only when every subject is set - the
					// truthy narrowing is the union of each subject's own truthy
					// chain narrowing, composed directly from the captured results
					if ($context->true()) {
						$types = new SpecifiedTypes();
						foreach ($expr->vars as $var) {
							$types = $types->unionWith(
								$this->defaultNarrowingHelper->createIssetTruthyChainTypes($s, $var, $readType, $expr, $context),
							);
						}

						return $types->setRootExpr($expr);
					}

					// non-true contexts (only SOME subject is unset): fold the
					// subjects through the conjunction narrowing; the fabricated
					// Isset_/BooleanAnd nodes are only printed into holder keys,
					// never walked
					$makeSubjectTypes = function (Expr $var, ExpressionResult $varResult) use ($nodeScopeResolver, $chainResults, $expr): Closure {
						return function (MutatingScope $scope, TypeSpecifierContext $ctx) use ($nodeScopeResolver, $chainResults, $expr, $var, $varResult): SpecifiedTypes {
							$scopedReadType = $this->defaultNarrowingHelper->buildChainTypeReader($chainResults, $scope, $nodeScopeResolver);
							if ($ctx->null()) {
								return $this->defaultNarrowingHelper->specifyDefaultTypes(new Isset_([$var], $expr->getAttributes()), $ctx);
							}
							if (!$ctx->true()) {
								return $this->defaultNarrowingHelper->createIssetSingleSubjectNonTrueTypes($scope, $var, $varResult, $scopedReadType, $ctx, $expr);
							}

							return $this->defaultNarrowingHelper->createIssetTruthyChainTypes($scope, $var, $scopedReadType, $expr, $ctx);
						};
					};

					$accExpr = new Isset_([$expr->vars[0]], $expr->getAttributes());
					$accTypes = $makeSubjectTypes($expr->vars[0], $varResults[0]);
					$accTruthyScope = $s->applySpecifiedTypes($accTypes($s, TypeSpecifierContext::createTruthy()));
					$accFalseyScope = $s->applySpecifiedTypes($accTypes($s, TypeSpecifierContext::createFalsey()));

					for ($i = 1, $varCount = count($expr->vars); $i < $varCount; $i++) {
						$rightExprNode = new Isset_([$expr->vars[$i]], $expr->getAttributes());
						$rightTypes = $makeSubjectTypes($expr->vars[$i], $varResults[$i]);
						$rightFalseyScope = $accTruthyScope->applySpecifiedTypes($rightTypes($accTruthyScope, TypeSpecifierContext::createFalsey()));

						$leftExprNode = $accExpr;
						$leftTypes = $accTypes;
						$leftTruthyScope = $accTruthyScope;
						$leftFalseyScope = $accFalseyScope;
						$accTypes = fn (MutatingScope $scope, TypeSpecifierContext $ctx): SpecifiedTypes => $this->booleanNarrowingHelper->specifyConjunction(
							$nodeScopeResolver,
							$scope,
							$ctx,
							$expr,
							$leftExprNode,
							$leftTypes,
							$leftTruthyScope,
							$leftFalseyScope,
							$rightExprNode,
							$rightTypes,
							$rightFalseyScope,
						);
						$accExpr = new BooleanAnd($leftExprNode, $rightExprNode);
						$accTruthyScope = $accTruthyScope->applySpecifiedTypes($rightTypes($accTruthyScope, TypeSpecifierContext::createTruthy()));
						$accFalseyScope = $s->applySpecifiedTypes($accTypes($s, TypeSpecifierContext::createFalsey()));
					}

					return $accTypes($s, $context)->setRootExpr($expr);
				}

				$issetExpr = $expr->vars[0];

				if (!$context->true()) {
					return $this->defaultNarrowingHelper->createIssetSingleSubjectNonTrueTypes($s, $issetExpr, $varResults[0], $readType, $context, $expr);
				}

				return $this->defaultNarrowingHelper->createIssetTruthyChainTypes($s, $issetExpr, $readType, $expr, $context);
			},
		);
	}


}
