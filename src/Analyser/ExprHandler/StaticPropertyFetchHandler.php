<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\Identical;
use PhpParser\Node\Expr\StaticPropertyFetch;
use PhpParser\Node\Name;
use PhpParser\Node\Scalar\String_;
use PhpParser\Node\Stmt;
use PhpParser\Node\VarLikeIdentifier;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\ImpurePoint;
use PHPStan\Analyser\IssetabilityDescriptor;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Rules\Properties\FoundPropertyReflection;
use PHPStan\Rules\Properties\PropertyReflectionFinder;
use PHPStan\Type\ErrorType;
use PHPStan\Type\MixedType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use function array_map;
use function array_merge;
use function count;

/**
 * @implements ExprHandler<StaticPropertyFetch>
 */
#[AutowiredService]
final class StaticPropertyFetchHandler implements ExprHandler
{

	public function __construct(
		private PropertyReflectionFinder $propertyReflectionFinder,
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof StaticPropertyFetch;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		$hasYield = false;
		$throwPoints = [];
		$impurePoints = [
			new ImpurePoint(
				$scope,
				$expr,
				'staticPropertyAccess',
				'static property access',
				true,
			),
		];
		$isAlwaysTerminating = false;
		$classResult = null;
		if ($expr->class instanceof Expr) {
			$classResult = $nodeScopeResolver->processExprNode($stmt, $expr->class, $scope, $storage, $nodeCallback, $context->enterDeep());
			$hasYield = $classResult->hasYield();
			$throwPoints = $classResult->getThrowPoints();
			$impurePoints = $classResult->getImpurePoints();
			$isAlwaysTerminating = $classResult->isAlwaysTerminating();
			$scope = $classResult->getScope();
		}
		$nameResult = null;
		if (!$expr->name instanceof VarLikeIdentifier) {
			$nameResult = $nodeScopeResolver->processExprNode($stmt, $expr->name, $scope, $storage, $nodeCallback, $context->enterDeep());
			$hasYield = $hasYield || $nameResult->hasYield();
			$throwPoints = array_merge($throwPoints, $nameResult->getThrowPoints());
			$impurePoints = array_merge($impurePoints, $nameResult->getImpurePoints());
			$isAlwaysTerminating = $isAlwaysTerminating || $nameResult->isAlwaysTerminating();
			$scope = $nameResult->getScope();
		}

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $hasYield,
			isAlwaysTerminating: $isAlwaysTerminating,
			throwPoints: $throwPoints,
			impurePoints: $impurePoints,
			containsNullsafe: $classResult !== null && $classResult->containsNullsafe(),
			issetabilityDescriptor: IssetabilityDescriptor::property($classResult, fn (MutatingScope $s): ?FoundPropertyReflection => $this->propertyReflectionFinder->findPropertyReflectionFromNode($expr, $s), $expr),
			typeCallback: function (MutatingScope $s) use ($expr, $classResult, $nameResult, $nodeScopeResolver): Type {
				$shortCircuit = static fn (Type $type): Type => $classResult !== null && $classResult->containsNullsafe() && TypeCombinator::containsNull($classResult->getTypeForScope($s))
					? TypeCombinator::addNull($type)
					: $type;

				if ($expr->name instanceof VarLikeIdentifier) {
					if ($s->nativeTypesPromoted) {
						$propertyReflection = $this->propertyReflectionFinder->findPropertyReflectionFromNode($expr, $s);
						if ($propertyReflection === null) {
							return new ErrorType();
						}
						if (!$propertyReflection->hasNativeType()) {
							return new MixedType();
						}

						return $shortCircuit($propertyReflection->getNativeType());
					}

					if ($expr->class instanceof Name) {
						$staticPropertyFetchedOnType = $s->resolveTypeByName($expr->class);
					} else {
						$classType = $classResult !== null ? $classResult->getTypeForScope($s) : $nodeScopeResolver->readStoredOrPriceOnDemand($expr->class, $s);
						$staticPropertyFetchedOnType = TypeCombinator::removeNull($classType)->getObjectTypeOrClassStringObjectType();
					}

					$fetchType = $this->propertyFetchType(
						$s,
						$staticPropertyFetchedOnType,
						$expr->name->toString(),
						$expr,
					);
					if ($fetchType === null) {
						$fetchType = new ErrorType();
					}

					return $shortCircuit($fetchType);
				}

				$nameType = $nameResult !== null ? $nameResult->getTypeForScope($s) : $nodeScopeResolver->readStoredOrPriceOnDemand($expr->name, $s);
				if (count($nameType->getConstantStrings()) > 0) {
					return TypeCombinator::union(
						...array_map(static function ($constantString) use ($expr, $s, $nodeScopeResolver): Type {
							if ($constantString->getValue() === '') {
								return new ErrorType();
							}

							// a static property fetch with a concrete name on the
							// name-pinned scope is synthetic.
							$truthyScope = $s->applySpecifiedTypes($nodeScopeResolver->processExprOnDemand(new Identical($expr->name, new String_($constantString->getValue())), $s, new ExpressionResultStorage())->getSpecifiedTypesForScope($s, TypeSpecifierContext::createTruthy()));

							return $nodeScopeResolver->priceSyntheticOnDemand(
								new Expr\StaticPropertyFetch($expr->class, new VarLikeIdentifier($constantString->getValue())),
								$truthyScope,
							);
						}, $nameType->getConstantStrings()),
					);
				}

				return new MixedType();
			},
			specifyTypesCallback: fn (MutatingScope $s, TypeSpecifierContext $context): SpecifiedTypes => $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context),
		);
	}

	private function propertyFetchType(MutatingScope $scope, Type $fetchedOnType, string $propertyName, StaticPropertyFetch $propertyFetch): ?Type
	{
		$propertyReflection = $scope->getStaticPropertyReflection($fetchedOnType, $propertyName);
		if ($propertyReflection === null) {
			return null;
		}

		if ($scope->isInWriteExpressionAssign($propertyFetch)) {
			return $propertyReflection->getWritableType();
		}

		return $propertyReflection->getReadableType();
	}

}
