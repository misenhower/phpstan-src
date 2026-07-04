<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use PhpParser\Node\Expr;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Expr\AlwaysRememberedExpr;
use PHPStan\Type\Constant\ConstantBooleanType;
use PHPStan\Type\NullType;
use function in_array;

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

		// slices 1+2 cover comparisons against a null/true/false literal;
		// everything else falls back
		if ($left instanceof Expr\ConstFetch && in_array($left->name->toLowerString(), ['null', 'true', 'false'], true)) {
			$constantName = $left->name->toLowerString();
			$subject = $right;
			$subjectResult = $rightResult;
		} elseif ($right instanceof Expr\ConstFetch && in_array($right->name->toLowerString(), ['null', 'true', 'false'], true)) {
			$constantName = $right->name->toLowerString();
			$subject = $left;
			$subjectResult = $leftResult;
		} else {
			return null;
		}

		// function calls against a constant narrow their arguments too
		// (array_key_first($a) !== null makes $a non-empty, array_search(...)
		// !== false narrows the haystack) - not ported yet
		$unwrappedSubject = $subject instanceof AlwaysRememberedExpr ? $subject->getExpr() : $subject;
		if ($unwrappedSubject instanceof Expr\FuncCall) {
			return null;
		}

		if ($constantName === 'null') {
			return $this->defaultNarrowingHelper->createSubjectTypes(
				$evaluationScope,
				$subject,
				$subjectResult,
				new NullType(),
				$context,
			);
		}

		// a bool literal pins the constant through the entries and runs the
		// subject's own narrowing in the matching bool context - identity,
		// not truthiness: `=== false` is the false context, not falsey
		$types = $this->defaultNarrowingHelper->createSubjectTypes(
			$evaluationScope,
			$subject,
			$subjectResult,
			new ConstantBooleanType($constantName === 'true'),
			$context,
		);

		// a nullsafe chain that did not produce the constant may have
		// short-circuited instead - its own narrowing only holds when the
		// comparison succeeded
		if (!$context->true() && ($unwrappedSubject instanceof Expr\NullsafeMethodCall || $unwrappedSubject instanceof Expr\NullsafePropertyFetch)) {
			return $types;
		}

		$boolContext = $constantName === 'true' ? TypeSpecifierContext::createTrue() : TypeSpecifierContext::createFalse();

		return $types->unionWith($subjectResult->getSpecifiedTypesForScope(
			$evaluationScope,
			$context->true() ? $boolContext : $boolContext->negate(),
		));
	}

}
