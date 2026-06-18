<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\BooleanAnd;
use PhpParser\Node\Expr\BinaryOp\NotIdentical;
use PhpParser\Node\Expr\ConstFetch;
use PhpParser\Node\Expr\MethodCall;
use PhpParser\Node\Expr\NullsafeMethodCall;
use PhpParser\Node\Name;
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
use PHPStan\Analyser\TypeSpecifier;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Printer\ExprPrinter;
use PHPStan\Type\NullType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use function array_merge;

/**
 * @implements ExprHandler<NullsafeMethodCall>
 */
#[AutowiredService]
final class NullsafeMethodCallHandler implements ExprHandler
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
		return $expr instanceof NullsafeMethodCall;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		$scopeBeforeNullsafe = $scope;

		$nonNullabilityResult = $this->nonNullabilityHelper->ensureShallowNonNullability($nodeScopeResolver, $scope, $scope, $expr->var);
		$attributes = array_merge($expr->getAttributes(), ['virtualNullsafeMethodCall' => true]);
		unset($attributes[ExprPrinter::ATTRIBUTE_CACHE_KEY]);
		$methodCall = new MethodCall(
			$expr->var,
			$expr->name,
			$expr->args,
			$attributes,
		);
		$exprResult = $nodeScopeResolver->processExprNode(
			$stmt,
			$methodCall,
			$nonNullabilityResult->getScope(),
			$storage,
			$nodeCallback,
			$context,
		);
		$scope = $this->nonNullabilityHelper->revertNonNullability($exprResult->getScope(), $nonNullabilityResult->getSpecifiedExpressions());

		// the var was processed above as the receiver of $methodCall; read its
		// stored result on the original scope instead of re-walking via getType().
		$varType = $nodeScopeResolver->readStoredOrPriceOnDemand($expr->var, $scopeBeforeNullsafe);

		$varIsNull = $varType->isNull();
		if ($varIsNull->yes()) {
			// Arguments are never evaluated when the var is always null.
			$scope = $scopeBeforeNullsafe;
		} elseif ($varIsNull->maybe()) {
			// Arguments might not be evaluated (short-circuit).
			// Merge with the original scope so variables assigned in arguments become "maybe defined".
			$scope = $scope->mergeWith($scopeBeforeNullsafe);
		}

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $exprResult->hasYield(),
			isAlwaysTerminating: false,
			throwPoints: $exprResult->getThrowPoints(),
			impurePoints: $exprResult->getImpurePoints(),
			containsNullsafe: true,
			typeCallback: static function (MutatingScope $s) use ($expr, $exprResult, $nodeScopeResolver): Type {
				// the var was processed above as the receiver of $methodCall.
				$varType = $nodeScopeResolver->readStoredOrPriceOnDemand($expr->var, $s);
				if ($varType->isNull()->yes()) {
					return new NullType();
				}
				if (!TypeCombinator::containsNull($varType)) {
					return $exprResult->getTypeForScope($s);
				}

				// the plain method call on the null-removed scope is synthetic.
				$truthyScope = $s->filterByTruthyValue(new NotIdentical($expr->var, new ConstFetch(new Name('null'))));

				return TypeCombinator::union(
					$nodeScopeResolver->priceSyntheticOnDemand(new MethodCall($expr->var, $expr->name, $expr->args), $truthyScope),
					new NullType(),
				);
			},
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr, $methodCall): SpecifiedTypes {
				if ($context->null()) {
					return $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
				}

				$types = $this->typeSpecifier->specifyTypesInCondition(
					$s,
					new BooleanAnd(
						new NotIdentical($expr->var, new ConstFetch(new Name('null'))),
						$methodCall,
					),
					$context,
				)->setRootExpr($expr);

				$nullSafeTypes = $this->typeSpecifier->handleDefaultTruthyOrFalseyContext($context, $expr, $s);
				return $context->true() ? $types->unionWith($nullSafeTypes) : $types->normalize($s)->intersectWith($nullSafeTypes->normalize($s));
			},
		);
	}

}
