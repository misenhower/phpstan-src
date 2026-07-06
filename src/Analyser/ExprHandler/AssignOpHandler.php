<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use DivisionByZeroError;
use PHPStan\Type\MixedType;
use PhpParser\Node\Expr;
use PhpParser\Node\Expr\AssignOp;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\CoalesceCompositionHelper;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\ExprHandler\Helper\ImplicitToStringCallHelper;
use PHPStan\Analyser\InternalThrowPoint;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\NoopNodeCallback;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\CoalesceExpressionNode;
use PHPStan\Reflection\InitializerExprTypeResolver;
use PHPStan\ShouldNotHappenException;
use PHPStan\Type\Constant\ConstantIntegerType;
use PHPStan\Type\NullType;
use PHPStan\Type\ObjectType;
use PHPStan\Type\Type;
use function array_merge;
use function get_class;
use function is_string;
use function sprintf;

/**
 * @implements ExprHandler<AssignOp>
 */
#[AutowiredService]
final class AssignOpHandler implements ExprHandler
{

	public function __construct(
		private AssignHandler $assignHandler,
		private InitializerExprTypeResolver $initializerExprTypeResolver,
		private ImplicitToStringCallHelper $implicitToStringCallHelper,
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
		private CoalesceCompositionHelper $coalesceCompositionHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof AssignOp;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;

		if (
			!$expr instanceof Expr\AssignOp\Coalesce
			&& ($expr->var instanceof Expr\Variable
				|| $expr->var instanceof Expr\PropertyFetch
				|| $expr->var instanceof Expr\StaticPropertyFetch)
		) {
			// `$lvalue OP= ...` reads the old value of `$lvalue`; processAssignVar()
			// processes a Variable/property target only as an assignment target, never
			// the whole lvalue as a read, so it never stores its ExpressionResult.
			// Process it here as a read so the typeCallback below consumes the stored
			// result instead of pricing the unprocessed lvalue on demand (single-pass
			// inside-out). The NoopNodeCallback avoids duplicate reports:
			// processAssignVar() already presents the target (and its sub-expressions)
			// to the node callback. (An ArrayDimFetch target is stored by
			// processAssignVar itself, so it is left out here.)
			$nodeScopeResolver->processExprNode($stmt, $expr->var, $scope, $storage, new NoopNodeCallback(), $context->enterDeep());
		}

		$varReadResult = null;
		$chainResults = [];
		$rhsResult = null;
		if ($expr instanceof Expr\AssignOp\Coalesce) {
			// the ??= left is otherwise processed only as an assignment target,
			// which carries no isset descriptor (bug-13623); price it once as a
			// read into a throwaway storage and capture the results (not the
			// storage) for the callbacks below - keeping the pre-read out of the
			// long-lived shared storage, whose result<->storage cycles would
			// otherwise accumulate across every ??= in the file
			$varStorage = new ExpressionResultStorage();
			$varReadResult = $nodeScopeResolver->processExprOnDemand($expr->var, $beforeScope, $varStorage);
			$this->defaultNarrowingHelper->captureChainResults($expr->var, $varStorage, $chainResults);
		}

		$typeCallback = function (bool $nativeTypesPromoted) use ($expr, $nodeScopeResolver, $beforeScope, $varReadResult, $chainResults, &$rhsResult): Type {
			// $expr->var and $expr->expr were processed during this handler's
			// processExpr (the var as the assignment target, the value expr by the
			// inner closure below), so their ExpressionResults are stored - read
			// them instead of re-walking via Scope::getType().
			$getType = static fn (Expr $e): Type => $nodeScopeResolver->readTypeOfMaybeStored($e, $nativeTypesPromoted ? $beforeScope->doNotTreatPhpDocTypesAsCertain() : $beforeScope);

			if ($expr instanceof Expr\AssignOp\Coalesce) {
				// the implied `$var ?? $rhs` composed from the pre-read left result
				// ($varReadResult is set exactly under this Coalesce branch) and
				// the right side's walk result captured by the inner closure below
				if ($rhsResult === null) {
					// a fiber-suspended rule can ask before processAssignVar ran
					// the right side - price it here on the same left-is-null
					// scope the walk uses; the walk's own result replaces it once
					// the inner closure runs
					$rhsScope = $beforeScope->applySpecifiedTypes($this->defaultNarrowingHelper->createSubjectTypes($beforeScope, $expr->var, $varReadResult, new NullType(), TypeSpecifierContext::createTruthy()));
					$rhsResult = $nodeScopeResolver->processExprOnDemand($expr->expr, $rhsScope, new ExpressionResultStorage());
				}

				return $this->coalesceCompositionHelper->composeType(
					$nodeScopeResolver,
					$expr->var,
					$varReadResult,
					$rhsResult,
					$beforeScope,
					$chainResults,
					$expr,
					$nativeTypesPromoted,
				);
			}

			if ($expr instanceof Expr\AssignOp\Concat) {
				return $this->initializerExprTypeResolver->getConcatType($expr->var, $expr->expr, $getType);
			}

			if ($expr instanceof Expr\AssignOp\BitwiseAnd) {
				return $this->initializerExprTypeResolver->getBitwiseAndType($expr->var, $expr->expr, $getType);
			}

			if ($expr instanceof Expr\AssignOp\BitwiseOr) {
				return $this->initializerExprTypeResolver->getBitwiseOrType($expr->var, $expr->expr, $getType);
			}

			if ($expr instanceof Expr\AssignOp\BitwiseXor) {
				return $this->initializerExprTypeResolver->getBitwiseXorType($expr->var, $expr->expr, $getType);
			}

			if ($expr instanceof Expr\AssignOp\Div) {
				return $this->initializerExprTypeResolver->getDivType($expr->var, $expr->expr, $getType);
			}

			if ($expr instanceof Expr\AssignOp\Mod) {
				return $this->initializerExprTypeResolver->getModType($expr->var, $expr->expr, $getType);
			}

			if ($expr instanceof Expr\AssignOp\Plus) {
				return $this->initializerExprTypeResolver->getPlusType($expr->var, $expr->expr, $getType);
			}

			if ($expr instanceof Expr\AssignOp\Minus) {
				return $this->initializerExprTypeResolver->getMinusType($expr->var, $expr->expr, $getType);
			}

			if ($expr instanceof Expr\AssignOp\Mul) {
				return $this->initializerExprTypeResolver->getMulType($expr->var, $expr->expr, $getType);
			}

			if ($expr instanceof Expr\AssignOp\Pow) {
				return $this->initializerExprTypeResolver->getPowType($expr->var, $expr->expr, $getType);
			}

			if ($expr instanceof Expr\AssignOp\ShiftLeft) {
				return $this->initializerExprTypeResolver->getShiftLeftType($expr->var, $expr->expr, $getType);
			}

			if ($expr instanceof Expr\AssignOp\ShiftRight) {
				return $this->initializerExprTypeResolver->getShiftRightType($expr->var, $expr->expr, $getType);
			}

			throw new ShouldNotHappenException(sprintf('Unhandled %s', get_class($expr)));
		};
		$specifyTypesCallback = fn (MutatingScope $s, TypeSpecifierContext $context): SpecifiedTypes => $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
		$createTypesCallback = null;
		if ($expr instanceof Expr\AssignOp\Coalesce) {
			// a type constraint on `$x ??= y` constrains the assigned variable -
			// what TypeSpecifier::create() recovered by its AssignOp\Coalesce arm
			$createTypesCallback = fn (MutatingScope $cs, Type $constraintType, TypeSpecifierContext $cctx): SpecifiedTypes => $this->defaultNarrowingHelper->createSubjectTypes($cs, $expr->var, $nodeScopeResolver->findStoredResult($expr->var, $cs), $constraintType, $cctx);
		}

		// processAssignVar asks getType($expr) for the value to assign; store this
		// result first so it resolves from the typeCallback above rather than
		// re-processing the node on demand (which would recurse).
		$nodeScopeResolver->storeExpressionResult($storage, $expr, $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: false,
			isAlwaysTerminating: false,
			throwPoints: [],
			impurePoints: [],
			typeCallback: $typeCallback,
			specifyTypesCallback: $specifyTypesCallback,
			createTypesCallback: $createTypesCallback,
		));

		$assignResult = $this->assignHandler->processAssignVar(
			$nodeScopeResolver,
			$scope,
			$storage,
			$stmt,
			$expr->var,
			$expr,
			$nodeCallback,
			$context,
			function (MutatingScope $scope) use ($stmt, $expr, $nodeCallback, $context, $storage, $nodeScopeResolver, $varReadResult, &$rhsResult): ExpressionResult {
				$originalScope = $scope;
				if ($expr instanceof Expr\AssignOp\Coalesce) {
					if ($varReadResult === null) {
						throw new ShouldNotHappenException();
					}
					// "var === null" for the right side's scope - the
					// identical-narrowing null slice composed from the pre-read
					// result (NotIdentical falsey = Identical truthy), no
					// synthetic NotIdentical walk
					$scope = $scope->applySpecifiedTypes($this->defaultNarrowingHelper->createSubjectTypes($scope, $expr->var, $varReadResult, new NullType(), TypeSpecifierContext::createTruthy()));

					if ($expr->var instanceof Expr\Variable && is_string($expr->var->name)) {
						$context = $context->enterRightSideAssign(
							$expr->var->name,
							$expr->expr,
						);
					}
				}

				$exprResult = $nodeScopeResolver->processExprNode($stmt, $expr->expr, $scope, $storage, $nodeCallback, $context->enterDeep());
				if ($expr instanceof Expr\AssignOp\Coalesce) {
					$rhsResult = $exprResult;
					$isAlwaysTerminating = $exprResult->isAlwaysTerminating() && $nodeScopeResolver->readTypeOfMaybeStored($expr->var, $originalScope)->isNull()->yes();
					return $this->expressionResultFactory->create(
						$exprResult->getScope()->mergeWith($originalScope),
						$originalScope,
						$expr->expr,
						$exprResult->hasYield(),
						$isAlwaysTerminating,
						$exprResult->getThrowPoints(),
						$exprResult->getImpurePoints(),
						typeCallback: static fn () => new MixedType(),
						specifyTypesCallback: static fn () => new SpecifiedTypes(),
					);
				}

				return $exprResult;
			},
			$expr instanceof Expr\AssignOp\Coalesce,
		);
		$scope = $assignResult->getScope();
		$throwPoints = $assignResult->getThrowPoints();
		$impurePoints = $assignResult->getImpurePoints();
		if (
			($expr instanceof Expr\AssignOp\Div || $expr instanceof Expr\AssignOp\Mod) &&
			!$nodeScopeResolver->readStoredResult($expr->expr, $storage)->getTypeOnScope($scope, false)->toNumber()->isSuperTypeOf(new ConstantIntegerType(0))->no()
		) {
			$throwPoints[] = InternalThrowPoint::createExplicit($scope, new ObjectType(DivisionByZeroError::class), $expr, false);
		}
		if ($expr instanceof Expr\AssignOp\Concat) {
			$toStringResult = $this->implicitToStringCallHelper->processImplicitToStringCall($nodeScopeResolver, $expr->expr, $scope);
			$throwPoints = array_merge($throwPoints, $toStringResult->getThrowPoints());
			$impurePoints = array_merge($impurePoints, $toStringResult->getImpurePoints());
		}

		if ($expr instanceof Expr\AssignOp\Coalesce) {
			if ($varReadResult === null) {
				throw new ShouldNotHappenException();
			}
			// NullCoalesceRule gets the chain's IssetabilityResolution off the
			// pre-read result carried by the node
			$nodeScopeResolver->callNodeCallbackWithExpression($nodeCallback, new CoalesceExpressionNode($expr, $varReadResult, 'on left side of ??='), $beforeScope, $storage, $context);
		}

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $assignResult->hasYield(),
			isAlwaysTerminating: $assignResult->isAlwaysTerminating(),
			throwPoints: $throwPoints,
			impurePoints: $impurePoints,
			typeCallback: $typeCallback,
			specifyTypesCallback: $specifyTypesCallback,
			createTypesCallback: $createTypesCallback,
		);
	}

}
