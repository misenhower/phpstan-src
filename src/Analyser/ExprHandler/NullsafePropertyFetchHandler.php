<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\BooleanAnd;
use PhpParser\Node\Expr\BinaryOp\NotIdentical;
use PhpParser\Node\Expr\ConstFetch;
use PhpParser\Node\Expr\NullsafePropertyFetch;
use PhpParser\Node\Expr\PropertyFetch;
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
 * @implements ExprHandler<NullsafePropertyFetch>
 */
#[AutowiredService]
final class NullsafePropertyFetchHandler implements ExprHandler
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
		return $expr instanceof NullsafePropertyFetch;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		$nonNullabilityResult = $this->nonNullabilityHelper->ensureShallowNonNullability($scope, $scope, $expr->var);
		$attributes = array_merge($expr->getAttributes(), ['virtualNullsafePropertyFetch' => true]);
		unset($attributes[ExprPrinter::ATTRIBUTE_CACHE_KEY]);
		$propertyFetch = new PropertyFetch(
			$expr->var,
			$expr->name,
			$attributes,
		);
		$exprResult = $nodeScopeResolver->processExprNode($stmt, $propertyFetch, $nonNullabilityResult->getScope(), $storage, $nodeCallback, $context);
		$scope = $this->nonNullabilityHelper->revertNonNullability($exprResult->getScope(), $nonNullabilityResult->getSpecifiedExpressions());

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
				// the var was processed above as the receiver of $propertyFetch -
				// read its stored result instead of re-walking via Scope::getType().
				$varType = $nodeScopeResolver->readStoredOrPriceOnDemand($expr->var, $s);
				if ($varType->isNull()->yes()) {
					return new NullType();
				}
				if (!TypeCombinator::containsNull($varType)) {
					return $exprResult->getTypeForScope($s);
				}

				// the plain property fetch on the null-removed scope is synthetic.
				$truthyScope = $s->filterByTruthyValue(new NotIdentical($expr->var, new ConstFetch(new Name('null'))));

				return TypeCombinator::union(
					$nodeScopeResolver->priceSyntheticOnDemand(new PropertyFetch($expr->var, $expr->name), $truthyScope),
					new NullType(),
				);
			},
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr, $propertyFetch): SpecifiedTypes {
				if ($context->null()) {
					return $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
				}

				$types = $this->typeSpecifier->specifyTypesInCondition(
					$s,
					new BooleanAnd(
						new NotIdentical($expr->var, new ConstFetch(new Name('null'))),
						$propertyFetch,
					),
					$context,
				)->setRootExpr($expr);

				$nullSafeTypes = $this->typeSpecifier->handleDefaultTruthyOrFalseyContext($context, $expr, $s);
				return $context->true() ? $types->unionWith($nullSafeTypes) : $types->normalize($s)->intersectWith($nullSafeTypes->normalize($s));
			},
		);
	}

}
