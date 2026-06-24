<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

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
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\ExprHandler\Helper\NonNullabilityHelper;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\NoopNodeCallback;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifier;
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
		private TypeSpecifier $typeSpecifier,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
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

			$varType = $nodeScopeResolver->readStoredOrPriceOnDemand($var->var, $scope);
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
		// getTypeForScope() instead of re-walking through Scope::getType().
		$chainResults = [];
		foreach ($expr->vars as $var) {
			$this->captureChainResults($var, $storage, $chainResults);
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
			typeCallback: static function (MutatingScope $s) use ($varResults): Type {
				$issetResult = true;
				foreach ($varResults as $varResult) {
					$result = $varResult->getIssetabilityResolution($s, false)->isSet(static function (Type $type): ?bool {
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
				$readType = static function (Expr $e) use ($chainResults, $s, $nodeScopeResolver): Type {
					$result = $chainResults[spl_object_id($e)] ?? null;

					return $result !== null ? $result->getTypeForScope($s) : $nodeScopeResolver->readStoredOrPriceOnDemand($e, $s);
				};

				if (count($expr->vars) === 0 || $context->null()) {
					return $this->typeSpecifier->specifyDefaultTypes($s, $expr, $context);
				}

				// rewrite multi param isset() to and-chained single param isset()
				if (count($expr->vars) > 1) {
					$issets = [];
					foreach ($expr->vars as $var) {
						$issets[] = new Isset_([$var], $expr->getAttributes());
					}

					$first = array_shift($issets);
					$andChain = null;
					foreach ($issets as $isset) {
						if ($andChain === null) {
							$andChain = new BooleanAnd($first, $isset);
							continue;
						}

						$andChain = new BooleanAnd($andChain, $isset);
					}

					if ($andChain === null) {
						throw new ShouldNotHappenException();
					}

					return $this->typeSpecifier->specifyTypesInCondition($s, $andChain, $context)->setRootExpr($expr);
				}

				$issetExpr = $expr->vars[0];

				if (!$context->true()) {
					$isset = $varResults[0]->getIssetabilityResolution($s, false)->isSet(static fn (): bool => true);

					if ($isset === false) {
						return new SpecifiedTypes();
					}

					$type = $readType($issetExpr);
					$isNullable = !$type->isNull()->no();
					$exprType = $this->defaultNarrowingHelper->createForSubject(
						$issetExpr,
						new NullType(),
						$context->negate(),
						$s,
					)->setRootExpr($expr);

					if ($issetExpr instanceof Expr\Variable && is_string($issetExpr->name)) {
						if ($isset === true) {
							if ($isNullable) {
								return $exprType;
							}

							// variable cannot exist in !isset()
							return $exprType->unionWith($this->defaultNarrowingHelper->createForSubject(
								new IssetExpr($issetExpr),
								new NullType(),
								$context,
								$s,
							))->setRootExpr($expr);
						}

						if ($isNullable) {
							// reduces variable certainty to maybe
							return $exprType->unionWith($this->defaultNarrowingHelper->createForSubject(
								new IssetExpr($issetExpr),
								new NullType(),
								$context->negate(),
								$s,
							))->setRootExpr($expr);
						}

						// variable cannot exist in !isset()
						return $this->defaultNarrowingHelper->createForSubject(
							new IssetExpr($issetExpr),
							new NullType(),
							$context,
							$s,
						)->setRootExpr($expr);
					}

					if ($isNullable && $isset === true) {
						return $exprType;
					}

					if (
						$issetExpr instanceof ArrayDimFetch
						&& $issetExpr->dim !== null
					) {
						$varType = $readType($issetExpr->var);
						if (!$varType instanceof MixedType) {
							$dimType = $readType($issetExpr->dim);

							if ($dimType instanceof ConstantIntegerType || $dimType instanceof ConstantStringType) {
								$constantArrays = $varType->getConstantArrays();
								$typesToRemove = [];
								foreach ($constantArrays as $constantArray) {
									$hasOffset = $constantArray->hasOffsetValueType($dimType);
									if (!$hasOffset->yes() || !$constantArray->getOffsetValueType($dimType)->isNull()->no()) {
										continue;
									}

									$typesToRemove[] = $constantArray;
								}

								if ($typesToRemove !== []) {
									$typeToRemove = TypeCombinator::union(...$typesToRemove);

									$result = $this->defaultNarrowingHelper->createForSubject(
										$issetExpr->var,
										$typeToRemove,
										TypeSpecifierContext::createFalse(),
										$s,
									)->setRootExpr($expr);

									if ($s->hasExpressionType($issetExpr->var)->maybe()) {
										$result = $result->unionWith(
											$this->defaultNarrowingHelper->createForSubject(
												new IssetExpr($issetExpr->var),
												new NullType(),
												TypeSpecifierContext::createTruthy(),
												$s,
											)->setRootExpr($expr),
										);
									}

									return $result;
								}
							}
						}
					}

					return new SpecifiedTypes();
				}

				$tmpVars = [$issetExpr];
				while (
					$issetExpr instanceof ArrayDimFetch
					|| $issetExpr instanceof PropertyFetch
					|| (
						$issetExpr instanceof StaticPropertyFetch
						&& $issetExpr->class instanceof Expr
					)
				) {
					if ($issetExpr instanceof StaticPropertyFetch) {
						/** @var Expr $issetExpr */
						$issetExpr = $issetExpr->class;
					} else {
						$issetExpr = $issetExpr->var;
					}
					$tmpVars[] = $issetExpr;
				}
				$vars = array_reverse($tmpVars);

				$types = new SpecifiedTypes();
				foreach ($vars as $var) {

					if ($var instanceof Expr\Variable && is_string($var->name)) {
						if ($s->hasVariableType($var->name)->no()) {
							return (new SpecifiedTypes([], []))->setRootExpr($expr);
						}
					}

					if (
						$var instanceof ArrayDimFetch
						&& $var->dim !== null
						&& !$readType($var->var) instanceof MixedType
					) {
						$dimType = $readType($var->dim);

						if ($dimType instanceof ConstantIntegerType || $dimType instanceof ConstantStringType) {
							$types = $types->unionWith(
								$this->defaultNarrowingHelper->createForSubject(
									$var->var,
									new HasOffsetType($dimType),
									$context,
									$s,
								)->setRootExpr($expr),
							);
						} else {
							$varType = $readType($var->var);

							$narrowedKey = AllowedArrayKeysTypes::narrowOffsetKeyType($varType, $dimType);
							if ($narrowedKey !== null) {
								$types = $types->unionWith(
									$this->defaultNarrowingHelper->createForSubject(
										$var->dim,
										$narrowedKey,
										$context,
										$s,
									)->setRootExpr($expr),
								);
							}

							if ($varType->isArray()->yes()) {
								$types = $types->unionWith(
									$this->defaultNarrowingHelper->createForSubject(
										$var->var,
										new NonEmptyArrayType(),
										$context,
										$s,
									)->setRootExpr($expr),
								);
							}
						}
					}

					if (
						$var instanceof PropertyFetch
						&& $var->name instanceof Identifier
					) {
						$types = $types->unionWith(
							$this->defaultNarrowingHelper->createForSubject($var->var, new IntersectionType([
								new ObjectWithoutClassType(),
								new HasPropertyType($var->name->toString()),
							]), TypeSpecifierContext::createTruthy(), $s)->setRootExpr($expr),
						);
					} elseif (
						$var instanceof StaticPropertyFetch
						&& $var->class instanceof Expr
						&& $var->name instanceof VarLikeIdentifier
					) {
						$types = $types->unionWith(
							$this->defaultNarrowingHelper->createForSubject($var->class, new IntersectionType([
								new ObjectWithoutClassType(),
								new HasPropertyType($var->name->toString()),
							]), TypeSpecifierContext::createTruthy(), $s)->setRootExpr($expr),
						);
					}

					$types = $types->unionWith(
						$this->defaultNarrowingHelper->createForSubject($var, new NullType(), TypeSpecifierContext::createFalse(), $s)->setRootExpr($expr),
					);
				}

				return $types;
			},
		);
	}

	/**
	 * @param array<int, ExpressionResult> $chainResults
	 */
	private function captureChainResults(Expr $node, ExpressionResultStorage $storage, array &$chainResults): void
	{
		$result = $storage->findExpressionResult($node);
		if ($result !== null) {
			$chainResults[spl_object_id($node)] = $result;
		}

		if ($node instanceof ArrayDimFetch) {
			$this->captureChainResults($node->var, $storage, $chainResults);
			if ($node->dim !== null) {
				$this->captureChainResults($node->dim, $storage, $chainResults);
			}
		} elseif ($node instanceof PropertyFetch) {
			$this->captureChainResults($node->var, $storage, $chainResults);
		} elseif ($node instanceof StaticPropertyFetch && $node->class instanceof Expr) {
			$this->captureChainResults($node->class, $storage, $chainResults);
		}
	}

}
