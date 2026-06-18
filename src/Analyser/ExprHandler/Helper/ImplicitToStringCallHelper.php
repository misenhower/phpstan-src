<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use PhpParser\Node\Expr;
use PhpParser\Node\Identifier;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ImpurePoint;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Php\PhpVersion;
use function sprintf;

#[AutowiredService]
final class ImplicitToStringCallHelper
{

	public function __construct(
		private PhpVersion $phpVersion,
		private MethodThrowPointHelper $methodThrowPointHelper,
		private ExpressionResultFactory $expressionResultFactory,
	)
	{
	}

	public function processImplicitToStringCall(NodeScopeResolver $nodeScopeResolver, Expr $expr, MutatingScope $scope): ExpressionResult
	{
		$throwPoints = [];
		$impurePoints = [];

		// the expression was processed before this call; read its stored result
		// or price it on demand instead of re-walking via Scope::getType().
		$exprType = $nodeScopeResolver->readStoredOrPriceOnDemand($expr, $scope);

		$toStringMethod = null;
		if (!$exprType->isObject()->no()) {
			$toStringMethod = $scope->getMethodReflection($exprType, '__toString');
		}
		if ($toStringMethod === null) {
			return $this->expressionResultFactory->create(
				$scope,
				beforeScope: $scope,
				expr: $expr,
				hasYield: false,
				isAlwaysTerminating: false,
				throwPoints: [],
				impurePoints: [],
			);
		}

		if (!$toStringMethod->hasSideEffects()->no()) {
			$impurePoints[] = new ImpurePoint(
				$scope,
				$expr,
				'methodCall',
				sprintf('call to method %s::%s()', $toStringMethod->getDeclaringClass()->getDisplayName(), $toStringMethod->getName()),
				$toStringMethod->isPure()->no(),
			);
		}

		if ($this->phpVersion->throwsOnStringCast()) {
			// the __toString() call is a synthetic node - price it on demand to
			// resolve its return type instead of re-walking via Scope::getType().
			$toStringCall = new Expr\MethodCall($expr, new Identifier('__toString'));
			$throwPoint = $this->methodThrowPointHelper->getThrowPoint(
				$toStringMethod,
				$toStringMethod->getOnlyVariant(),
				$toStringCall,
				$scope,
				ExpressionContext::createDeep(),
				$nodeScopeResolver->priceSyntheticOnDemand($toStringCall, $scope),
			);
			if ($throwPoint !== null) {
				$throwPoints[] = $throwPoint;
			}
		}

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $scope,
			expr: $expr,
			hasYield: false,
			isAlwaysTerminating: false,
			throwPoints: $throwPoints,
			impurePoints: $impurePoints,
		);
	}

}
