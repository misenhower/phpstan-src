<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use DivisionByZeroError;
use PHPStan\Type\MixedType;
use PhpParser\Node\Expr;
use PhpParser\Node\Expr\AssignOp;
use PhpParser\Node\Expr\BinaryOp;
use PhpParser\Node\Expr\ConstFetch;
use PhpParser\Node\Name;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
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

		$typeCallback = function (bool $nativeTypesPromoted) use ($expr, $nodeScopeResolver, $beforeScope): Type {
			// $expr->var and $expr->expr were processed during this handler's
			// processExpr (the var as the assignment target, the value expr by the
			// inner closure below), so their ExpressionResults are stored - read
			// them instead of re-walking via Scope::getType().
			$getType = static fn (Expr $e): Type => $nodeScopeResolver->readTypeOfMaybeStored($e, $nativeTypesPromoted ? $beforeScope->doNotTreatPhpDocTypesAsCertain() : $beforeScope);

			if ($expr instanceof Expr\AssignOp\Coalesce) {
				// The coalesce is synthetic; price it on demand. The ??= left is stored
				// as an assignment target (no isset descriptor), so inject a read result
				// of it (with the descriptor) - otherwise the coalesce resolves a
				// descriptor-less leaf that reads as definitely-set and drops the `??`
				// branch, losing the optional offset natively (bug-13623).
				$coalesce = new BinaryOp\Coalesce($expr->var, $expr->expr, $expr->getAttributes());
				$varReadResult = $nodeScopeResolver->processExprOnDemand($expr->var, $beforeScope, new ExpressionResultStorage());
				$coalesceStorage = ($beforeScope->getCurrentExpressionResultStorage() ?? new ExpressionResultStorage())->duplicate();
				$nodeScopeResolver->storeExpressionResult($coalesceStorage, $expr->var, $varReadResult);

				$coalesceResult = $nodeScopeResolver->processExprOnDemand($coalesce, $beforeScope, $coalesceStorage);

				return $nativeTypesPromoted ? $coalesceResult->getNativeType() : $coalesceResult->getType();
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
		$specifyTypesCallback = fn (TypeSpecifierContext $context, bool $nativeTypesPromoted): SpecifiedTypes => $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
		$createTypesCallback = null;
		if ($expr instanceof Expr\AssignOp\Coalesce) {
			// a type constraint on `$x ??= y` constrains the assigned variable -
			// what TypeSpecifier::create() recovered by its AssignOp\Coalesce arm
			$createTypesCallback = function (Type $constraintType, TypeSpecifierContext $cctx, bool $nativeTypesPromoted) use ($expr, $nodeScopeResolver, $beforeScope): SpecifiedTypes {
				$cs = $nativeTypesPromoted ? $beforeScope->doNotTreatPhpDocTypesAsCertain() : $beforeScope;

				return $this->defaultNarrowingHelper->createSubjectTypes($cs, $expr->var, $nodeScopeResolver->findStoredResult($expr->var, $cs), $constraintType, $cctx);
			};
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
			function (MutatingScope $scope) use ($stmt, $expr, $nodeCallback, $context, $storage, $nodeScopeResolver): ExpressionResult {
				$originalScope = $scope;
				if ($expr instanceof Expr\AssignOp\Coalesce) {
					$scope = $scope->applySpecifiedTypes($nodeScopeResolver->processExprOnDemand(new BinaryOp\NotIdentical($expr->var, new ConstFetch(new Name('null'))), $scope, new ExpressionResultStorage())->getSpecifiedTypesForScope($scope, TypeSpecifierContext::createFalsey()));

					if ($expr->var instanceof Expr\Variable && is_string($expr->var->name)) {
						$context = $context->enterRightSideAssign(
							$expr->var->name,
							$expr->expr,
						);
					}
				}

				$exprResult = $nodeScopeResolver->processExprNode($stmt, $expr->expr, $scope, $storage, $nodeCallback, $context->enterDeep());
				if ($expr instanceof Expr\AssignOp\Coalesce) {
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
						specifyTypesCallback: SpecifiedTypes::emptySpecifyCallback(),
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
			// the ??= left side is processed as an assignment target, not a read, so
			// it carries no isset descriptor; read it on demand so NullCoalesceRule
			// gets the chain's IssetabilityResolution off the carried result
			$varReadResult = $nodeScopeResolver->processExprOnDemand($expr->var, $beforeScope, new ExpressionResultStorage());
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
