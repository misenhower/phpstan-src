<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use PhpParser\Node\Expr;
use PhpParser\Node\Name;
use PhpParser\Node\Scalar;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Expr\AlwaysRememberedExpr;
use PHPStan\Type\Constant\ConstantBooleanType;
use PHPStan\Type\NeverType;
use PHPStan\Type\NullType;
use PHPStan\Type\Type;
use function count;
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

	/**
	 * @param callable(): Type $identicalTypeCallback the comparison's own type
	 *        in Identical semantics (the caller flips a NotIdentical verdict)
	 */
	public function specifyIdentical(
		Expr $left,
		Expr $right,
		ExpressionResult $leftResult,
		ExpressionResult $rightResult,
		TypeSpecifierContext $context,
		MutatingScope $evaluationScope,
		callable $identicalTypeCallback,
	): ?SpecifiedTypes
	{
		if ($context->null()) {
			return null;
		}

		// slices 1+2 cover comparisons against a null/true/false literal;
		// everything else falls through to the scalar-literal slice below
		if ($left instanceof Expr\ConstFetch && in_array($left->name->toLowerString(), ['null', 'true', 'false'], true)) {
			$constantName = $left->name->toLowerString();
			$subject = $right;
			$subjectResult = $rightResult;
		} elseif ($right instanceof Expr\ConstFetch && in_array($right->name->toLowerString(), ['null', 'true', 'false'], true)) {
			$constantName = $right->name->toLowerString();
			$subject = $left;
			$subjectResult = $leftResult;
		} else {
			return $this->specifyAgainstScalarLiteral($left, $right, $leftResult, $rightResult, $context, $evaluationScope, $identicalTypeCallback);
		}

		if (!$this->isSubjectCoveredAgainstConstant($subject)) {
			return null;
		}

		if ($constantName === 'null') {
			// deliberately NOT guarded by specifyDecidedComparison(): a decided
			// null comparison still emits its subtraction entry so assign-time
			// conditional holders fire ($id = $x?->prop; if ($id !== null) makes
			// $x non-null even when $id's own type already excludes null) - the
			// old path's blanket guard here is what kept bug-10482 red
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
		$unwrappedSubject = $subject instanceof AlwaysRememberedExpr ? $subject->getExpr() : $subject;
		if (!$context->true() && ($unwrappedSubject instanceof Expr\NullsafeMethodCall || $unwrappedSubject instanceof Expr\NullsafePropertyFetch)) {
			return $types;
		}

		$boolContext = $constantName === 'true' ? TypeSpecifierContext::createTrue() : TypeSpecifierContext::createFalse();

		return $types->unionWith($subjectResult->getSpecifiedTypesForScope(
			$evaluationScope,
			$context->true() ? $boolContext : $boolContext->negate(),
		));
	}

	/**
	 * Slice 3: comparisons against a scalar literal or a class constant
	 * (`$a === 5`, `$s === Foo::BAR`, `$suit === Suit::Hearts`) pin the
	 * single-valued side onto the other operand - the composed form of the
	 * finite-types narrowing at the tail of the old identical path.
	 */
	/**
	 * @param callable(): Type $identicalTypeCallback
	 */
	private function specifyAgainstScalarLiteral(
		Expr $left,
		Expr $right,
		ExpressionResult $leftResult,
		ExpressionResult $rightResult,
		TypeSpecifierContext $context,
		MutatingScope $evaluationScope,
		callable $identicalTypeCallback,
	): ?SpecifiedTypes
	{
		if ($this->isScalarLiteral($left)) {
			$constantExpr = $left;
			$constantResult = $leftResult;
			$subject = $right;
			$subjectResult = $rightResult;
		} elseif ($this->isScalarLiteral($right)) {
			$constantExpr = $right;
			$constantResult = $rightResult;
			$subject = $left;
			$subjectResult = $leftResult;
		} else {
			return null;
		}

		if (!$this->isSubjectCoveredAgainstConstant($subject)) {
			return null;
		}

		$decidedTypes = $this->specifyDecidedComparison($left, $right, $leftResult, $rightResult, $context, $evaluationScope, $identicalTypeCallback);
		if ($decidedTypes !== null) {
			return $decidedTypes;
		}

		$constantType = $constantResult->getTypeOnScope($evaluationScope, $evaluationScope->nativeTypesPromoted);
		if (count($constantType->getFiniteTypes()) !== 1) {
			// a class constant does not have to be single-valued
			return null;
		}

		$types = $this->defaultNarrowingHelper->createSubjectTypes(
			$evaluationScope,
			$subject,
			$subjectResult,
			$constantType,
			$context,
		);

		// a single-valued subject pins its value onto the literal side too
		$subjectType = $subjectResult->getTypeOnScope($evaluationScope, $evaluationScope->nativeTypesPromoted);
		if (count($subjectType->getFiniteTypes()) === 1) {
			$types = $types->unionWith($this->defaultNarrowingHelper->createSubjectTypes(
				$evaluationScope,
				$constantExpr,
				$constantResult,
				$subjectType,
				$context,
			));
		}

		return $types;
	}

	/**
	 * A statically decided comparison tells the false context nothing: the
	 * branch is dead on the certain flavour, and subtracting the constant
	 * would wrongly leak into the wider native flavour (mixed~'ab'). The
	 * NeverType entries mirror the old identical tail's no-op.
	 *
	 * @param callable(): Type $identicalTypeCallback
	 */
	private function specifyDecidedComparison(
		Expr $left,
		Expr $right,
		ExpressionResult $leftResult,
		ExpressionResult $rightResult,
		TypeSpecifierContext $context,
		MutatingScope $evaluationScope,
		callable $identicalTypeCallback,
	): ?SpecifiedTypes
	{
		if (!$context->false()) {
			return null;
		}

		$identicalType = $identicalTypeCallback();
		$isTrue = $identicalType->isTrue()->yes();
		if (!$isTrue && !$identicalType->isFalse()->yes()) {
			return null;
		}

		$never = new NeverType();
		$contextForTypes = $isTrue ? $context->negate() : $context;

		return $this->defaultNarrowingHelper->createSubjectTypes($evaluationScope, $left, $leftResult, $never, $contextForTypes)->unionWith(
			$this->defaultNarrowingHelper->createSubjectTypes($evaluationScope, $right, $rightResult, $never, $contextForTypes),
		);
	}

	private function isScalarLiteral(Expr $expr): bool
	{
		if ($expr instanceof Scalar\Int_ || $expr instanceof Scalar\String_ || $expr instanceof Scalar\Float_) {
			return true;
		}

		// Foo::BAR, Suit::Hearts, Foo::class - but not $a::class, whose
		// narrowing works on $a (an old-world block, not ported yet)
		return $expr instanceof Expr\ClassConstFetch
			&& $expr->class instanceof Name
			&& !$expr->name instanceof Expr;
	}

	/**
	 * Subjects whose comparison against a constant narrows more than the
	 * subject expression itself stay on the old-world path for now: function
	 * calls narrow their arguments (array_key_first($a) !== null makes $a
	 * non-empty, count($a) === 0 empties $a), `$a::class` narrows $a.
	 */
	private function isSubjectCoveredAgainstConstant(Expr $subject): bool
	{
		$unwrapped = $subject instanceof AlwaysRememberedExpr ? $subject->getExpr() : $subject;
		if ($unwrapped instanceof Expr\FuncCall) {
			return false;
		}

		return !($unwrapped instanceof Expr\ClassConstFetch && $unwrapped->class instanceof Expr);
	}

}
