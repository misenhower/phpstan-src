<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use PhpParser\Node\Expr;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Expr\AlwaysRememberedExpr;
use PHPStan\Type\NullType;

/**
 * New-world narrowing for `===` (and, via a negated context, `!==`): composed
 * from the operands' ExpressionResults, no scope asks and no synthetic nodes.
 * The evaluation scope is a create-time constant of the calling handler (it
 * carries the flavour and feeds entry composition), never the asking scope.
 *
 * Covers the identity comparisons incrementally; specifyIdentical() returns
 * null for a shape it does not handle yet and the caller falls back to the
 * old-world EqualityTypeSpecifyingHelper. The fallback dies with the last
 * uncovered shape.
 */
#[AutowiredService]
final class IdenticalNarrowingHelper
{

	public function __construct(
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function specifyIdentical(
		Expr $left,
		Expr $right,
		ExpressionResult $leftResult,
		ExpressionResult $rightResult,
		TypeSpecifierContext $context,
		MutatingScope $evaluationScope,
	): ?SpecifiedTypes
	{
		if ($context->null()) {
			return null;
		}

		// slice 1 covers comparisons against null; everything else falls back
		if ($left instanceof Expr\ConstFetch && $left->name->toLowerString() === 'null') {
			$subject = $right;
			$subjectResult = $rightResult;
		} elseif ($right instanceof Expr\ConstFetch && $right->name->toLowerString() === 'null') {
			$subject = $left;
			$subjectResult = $leftResult;
		} else {
			return null;
		}

		// function calls against null narrow their arguments too
		// (array_key_first($a) !== null makes $a non-empty) - not ported yet
		$unwrappedSubject = $subject instanceof AlwaysRememberedExpr ? $subject->getExpr() : $subject;
		if ($unwrappedSubject instanceof Expr\FuncCall) {
			return null;
		}

		return $this->defaultNarrowingHelper->createSubjectTypes(
			$evaluationScope,
			$subject,
			$subjectResult,
			new NullType(),
			$context,
		);
	}

}
