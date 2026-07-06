<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use PhpParser\Node\Expr;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Type\NullType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;

/**
 * Composes the `??` type and narrowing from the sides' walk results - shared
 * by CoalesceHandler and AssignOpHandler's `??=`, which has no real Coalesce
 * node to walk.
 */
#[AutowiredService]
final class CoalesceCompositionHelper
{

	public function __construct(
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	/**
	 * A falsey coalesce means its left side was null (when it was surely set).
	 */
	public function getFalseySpecifiedTypes(MutatingScope $s, Expr $leftExpr, ExpressionResult $leftResult, Expr $rootExpr, TypeSpecifierContext $context): SpecifiedTypes
	{
		$isset = $leftResult->getIssetabilityResolution($s, false)->isSet(static fn (): bool => true);

		if ($isset !== true) {
			return new SpecifiedTypes();
		}

		return $this->defaultNarrowingHelper->createSubjectTypes($s, $leftExpr, $leftResult, new NullType(), $context->negate())->setRootExpr($rootExpr);
	}

	/**
	 * The `??`'s own type: the left side when it is surely set and non-null,
	 * the right side when it surely is not, their union otherwise. Runs on the
	 * evaluation scope (where the sides were walked), not the asking scope.
	 *
	 * @param array<int, ExpressionResult> $chainResults
	 */
	public function composeType(
		NodeScopeResolver $nodeScopeResolver,
		Expr $leftExpr,
		ExpressionResult $leftResult,
		ExpressionResult $rightResult,
		MutatingScope $evaluationScope,
		array $chainResults,
		Expr $rootExpr,
		bool $nativeTypesPromoted,
	): Type
	{
		$result = $leftResult->getIssetabilityResolution($evaluationScope, false)->isSet(static function (Type $type): ?bool {
			$isNull = $type->isNull();
			if ($isNull->maybe()) {
				return null;
			}

			return !$isNull->yes();
		});

		// the left side's type when it is set: the left re-processed on the
		// left-is-set narrowed scope (a genuinely different scope than the
		// left's own - offsets resolve against the HasOffset-narrowed parent)
		$leftIsSetType = function () use ($leftExpr, $nodeScopeResolver, $evaluationScope, $chainResults, $rootExpr): Type {
			$leftIssetTypes = $this->defaultNarrowingHelper->createIssetTruthyChainTypes(
				$evaluationScope,
				$leftExpr,
				$this->defaultNarrowingHelper->buildChainTypeReader($chainResults, $evaluationScope, $nodeScopeResolver),
				$rootExpr,
				TypeSpecifierContext::createTruthy(),
			);

			return TypeCombinator::removeNull($nodeScopeResolver->processExprOnDemand($leftExpr, $evaluationScope->applySpecifiedTypes($leftIssetTypes), new ExpressionResultStorage())->getType());
		};

		if ($result !== null && $result !== false) {
			return $leftIsSetType();
		}

		// the right side was processed on the left-is-null scope, so its own
		// result is the evaluation point.
		$rightType = $nativeTypesPromoted ? $rightResult->getNativeType() : $rightResult->getType();

		if ($result === null) {
			return TypeCombinator::union($leftIsSetType(), $rightType);
		}

		return $rightType;
	}

}
