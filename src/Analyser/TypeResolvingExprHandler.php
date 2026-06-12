<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

use PhpParser\Node\Expr;
use PHPStan\Type\Type;

/**
 * @template T of Expr
 * @extends ExprHandler<T>
 */
interface TypeResolvingExprHandler extends ExprHandler
{

	/**
	 * @param T $expr
	 */
	public function resolveType(MutatingScope $scope, Expr $expr): Type;

	/**
	 * @param T $expr
	 */
	public function specifyTypes(
		TypeSpecifier $typeSpecifier,
		Scope $scope,
		Expr $expr,
		TypeSpecifierContext $context,
	): SpecifiedTypes;

}
