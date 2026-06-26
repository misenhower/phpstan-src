<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

use PhpParser\Node\Expr;
use PHPStan\Type\Type;

interface ExpressionResultFactory
{

	/**
	 * @param InternalThrowPoint[] $throwPoints
	 * @param ImpurePoint[] $impurePoints
	 * @param (callable(): MutatingScope)|null $truthyScopeCallback
	 * @param (callable(): MutatingScope)|null $falseyScopeCallback
	 * @param (callable(MutatingScope): Type)|null $typeCallback
	 * @param callable(MutatingScope, TypeSpecifierContext): SpecifiedTypes $specifyTypesCallback
	 * @param (callable(MutatingScope, Type, TypeSpecifierContext): SpecifiedTypes)|null $createTypesCallback
	 */
	public function create(
		MutatingScope $scope,
		MutatingScope $beforeScope,
		Expr $expr,
		bool $hasYield,
		bool $isAlwaysTerminating,
		array $throwPoints,
		array $impurePoints,
		?callable $typeCallback,
		callable $specifyTypesCallback,
		bool $containsNullsafe = false,
		?IssetabilityDescriptor $issetabilityDescriptor = null,
		?callable $truthyScopeCallback = null,
		?callable $falseyScopeCallback = null,
		?callable $createTypesCallback = null,
		?Type $type = null,
		?Type $nativeType = null,
	): ExpressionResult;

}
