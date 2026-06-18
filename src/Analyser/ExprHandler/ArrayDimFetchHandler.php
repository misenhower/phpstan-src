<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use ArrayAccess;
use PhpParser\Node\Arg;
use PhpParser\Node\Expr;
use PhpParser\Node\Expr\ArrayDimFetch;
use PhpParser\Node\Expr\MethodCall;
use PhpParser\Node\Identifier;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\IssetabilityDescriptor;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\NoopNodeCallback;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Expr\TypeExpr;
use PHPStan\Type\NeverType;
use PHPStan\Type\ObjectType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use function array_merge;

/**
 * @implements ExprHandler<ArrayDimFetch>
 */
#[AutowiredService]
final class ArrayDimFetchHandler implements ExprHandler
{

	public function __construct(
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof ArrayDimFetch;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		if ($expr->dim === null) {
			$varResult = $nodeScopeResolver->processExprNode($stmt, $expr->var, $scope, $storage, $nodeCallback, $context->enterDeep());
			$scope = $varResult->getScope();

			return $this->expressionResultFactory->create(
				$scope,
				beforeScope: $beforeScope,
				expr: $expr,
				hasYield: $varResult->hasYield(),
				isAlwaysTerminating: $varResult->isAlwaysTerminating(),
				throwPoints: $varResult->getThrowPoints(),
				impurePoints: $varResult->getImpurePoints(),
				containsNullsafe: $varResult->containsNullsafe(),
				// `$arr[]` only appears as an assignment target; reading it is a NeverType
				typeCallback: static fn (): Type => new NeverType(),
				specifyTypesCallback: fn (MutatingScope $s, TypeSpecifierContext $context): SpecifiedTypes => $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context),
			);
		}

		$dimResult = $nodeScopeResolver->processExprNode($stmt, $expr->dim, $scope, $storage, $nodeCallback, $context->enterDeep());
		$varResult = $nodeScopeResolver->processExprNode($stmt, $expr->var, $dimResult->getScope(), $storage, $nodeCallback, $context->enterDeep());
		$throwPoints = array_merge($dimResult->getThrowPoints(), $varResult->getThrowPoints());
		$impurePoints = array_merge($dimResult->getImpurePoints(), $varResult->getImpurePoints());
		$scope = $varResult->getScope();

		$varType = $varResult->getTypeForScope($scope);
		if (!$varType->isArray()->yes() && !(new ObjectType(ArrayAccess::class))->isSuperTypeOf($varType)->no()) {
			$throwPoints = array_merge($throwPoints, $nodeScopeResolver->processExprNode(
				$stmt,
				new MethodCall(new TypeExpr($varType), 'offsetGet'),
				$scope,
				$storage,
				new NoopNodeCallback(),
				$context,
			)->getThrowPoints());
		}

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $dimResult->hasYield() || $varResult->hasYield(),
			isAlwaysTerminating: $dimResult->isAlwaysTerminating() || $varResult->isAlwaysTerminating(),
			throwPoints: $throwPoints,
			impurePoints: $impurePoints,
			containsNullsafe: $varResult->containsNullsafe(),
			issetabilityDescriptor: IssetabilityDescriptor::offset($varResult, $dimResult),
			typeCallback: function (MutatingScope $s) use ($expr, $varResult, $dimResult): Type {
				$offsetAccessibleType = $varResult->getTypeForScope($s);
				$shortCircuit = static fn (Type $type): Type => $varResult->containsNullsafe() && TypeCombinator::containsNull($offsetAccessibleType)
					? TypeCombinator::addNull($type)
					: $type;

				if (
					!$offsetAccessibleType->isArray()->yes()
					&& (new ObjectType(ArrayAccess::class))->isSuperTypeOf($offsetAccessibleType)->yes()
				) {
					return $shortCircuit($s->getType(
						new MethodCall(
							$expr->var,
							new Identifier('offsetGet'),
							[
								new Arg($expr->dim),
							],
						),
					));
				}

				return $shortCircuit($offsetAccessibleType->getOffsetValueType($dimResult->getTypeForScope($s)));
			},
			specifyTypesCallback: fn (MutatingScope $s, TypeSpecifierContext $context): SpecifiedTypes => $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context),
		);
	}

}
