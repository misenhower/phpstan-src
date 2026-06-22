<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\ArrowFunction;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\ClosureTypeResolver;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;

/**
 * @implements ExprHandler<ArrowFunction>
 */
#[AutowiredService]
final class ArrowFunctionHandler implements ExprHandler
{

	public function __construct(
		private ClosureTypeResolver $closureTypeResolver,
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof ArrowFunction;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$result = $nodeScopeResolver->processArrowFunctionNode($stmt, $expr, $scope, $storage, $nodeCallback, null);

		// A plain typeCallback recursing through getClosureType() would re-walk
		// the body each getType() ask before the cache populates and hang;
		// ExpressionResult excludes closures from its tracked-type early return.
		// Compute the ClosureType once here and store it as an eager value. The
		// native flavour mirrors what getNativeType() did via resolveType() on a
		// promoted scope (getClosureType($scope->doNotTreatPhpDocTypesAsCertain())).
		$type = $this->closureTypeResolver->getClosureType($scope, $expr);
		$nativeType = $this->closureTypeResolver->getClosureType($scope->doNotTreatPhpDocTypesAsCertain(), $expr);

		return $this->expressionResultFactory->create(
			$result->getScope(),
			beforeScope: $scope,
			expr: $expr,
			hasYield: $result->hasYield(),
			isAlwaysTerminating: false,
			throwPoints: [],
			impurePoints: [],
			specifyTypesCallback: fn (MutatingScope $s, TypeSpecifierContext $c) => $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $c),
			type: $type,
			nativeType: $nativeType,
		);
	}

}
