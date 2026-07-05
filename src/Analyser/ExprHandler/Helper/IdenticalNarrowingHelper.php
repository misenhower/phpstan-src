<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use Countable;
use PhpParser\Node\Expr;
use PhpParser\Node\Name;
use PhpParser\Node\Scalar;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Expr\AlwaysRememberedExpr;
use PHPStan\Reflection\ReflectionProvider;
use PHPStan\Type\Accessory\AccessoryLowercaseStringType;
use PHPStan\Type\Accessory\AccessoryNonEmptyStringType;
use PHPStan\Type\Accessory\AccessoryNonFalsyStringType;
use PHPStan\Type\ArrayType;
use PHPStan\Type\BooleanType;
use PHPStan\Type\Accessory\AccessoryUppercaseStringType;
use PHPStan\Type\Accessory\NonEmptyArrayType;
use PHPStan\Type\Constant\ConstantArrayType;
use PHPStan\Type\Constant\ConstantBooleanType;
use PHPStan\Type\Constant\ConstantIntegerType;
use PHPStan\Type\Constant\ConstantStringType;
use PHPStan\Type\FloatType;
use PHPStan\Type\IntegerRangeType;
use PHPStan\Type\Generic\GenericClassStringType;
use PHPStan\Type\IntegerType;
use PHPStan\Type\IntersectionType;
use PHPStan\Type\MixedType;
use PHPStan\Type\NeverType;
use PHPStan\Type\NullType;
use PHPStan\Type\ObjectType;
use PHPStan\Type\ObjectWithoutClassType;
use PHPStan\Type\ResourceType;
use PHPStan\Type\StringType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use PHPStan\Type\UnionType;
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
		private ReflectionProvider $reflectionProvider,
		private CountNarrowingHelper $countNarrowingHelper,
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

		if ($constantName !== 'null' && !$this->isSubjectCoveredAgainstConstant($subject)) {
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

		$unwrappedSubject = $subject instanceof AlwaysRememberedExpr ? $subject->getExpr() : $subject;
		if ($unwrappedSubject instanceof Expr\FuncCall) {
			// get_class/get_debug_type compose below; other calls narrow their
			// arguments in ways not ported yet (count($a) === 0 empties $a)
			if (
				!($unwrappedSubject->name instanceof Name)
				|| $unwrappedSubject->isFirstClassCallable()
				|| !in_array($unwrappedSubject->name->toLowerString(), [
					'get_class', 'get_debug_type', 'gettype', 'preg_match', 'strlen', 'mb_strlen', 'count', 'sizeof',
					'substr', 'strstr', 'stristr', 'strchr', 'strrchr', 'strtolower', 'strtoupper', 'ucfirst', 'lcfirst',
					'mb_substr', 'mb_strstr', 'mb_stristr', 'mb_strchr', 'mb_strrchr', 'mb_strtolower', 'mb_strtoupper', 'mb_ucfirst', 'mb_lcfirst',
					'ucwords', 'mb_convert_case', 'mb_convert_kana',
					'trim', 'ltrim', 'rtrim', 'chop', 'mb_trim', 'mb_ltrim', 'mb_rtrim',
					'get_parent_class',
				], true)
				|| !isset($unwrappedSubject->getArgs()[0])
			) {
				return null;
			}
		} elseif (!$this->isSubjectCoveredAgainstConstant($subject)) {
			return null;
		}

		$constantType = $constantResult->getTypeOnScope($evaluationScope, $evaluationScope->nativeTypesPromoted);
		if (count($constantType->getFiniteTypes()) !== 1) {
			// a class constant does not have to be single-valued
			return null;
		}

		// preg_match(...) === 1 is the call's own truthy narrowing - the
		// type-specifying extensions narrow the by-ref \$matches argument
		if (
			$unwrappedSubject instanceof Expr\FuncCall
			&& $unwrappedSubject->name->toLowerString() === 'preg_match'
		) {
			if ($context->true() && (new ConstantIntegerType(1))->isSuperTypeOf($constantType)->yes()) {
				return $subjectResult->getSpecifiedTypesForScope($evaluationScope, $context);
			}

			// other constants and contexts only pin the call below
		}

		// a trimmed string that is not '' was a non-empty string already
		if (
			$unwrappedSubject instanceof Expr\FuncCall
			&& in_array($unwrappedSubject->name->toLowerString(), ['trim', 'ltrim', 'rtrim', 'chop', 'mb_trim', 'mb_ltrim', 'mb_rtrim'], true)
		) {
			if ($context->false()) {
				$constantStrings = $constantType->getConstantStrings();
				if (count($constantStrings) === 1 && $constantStrings[0]->getValue() === '') {
					$argExpr = $unwrappedSubject->getArgs()[0]->value;
					$argResult = $evaluationScope->getCurrentExpressionResultStorage()?->findExpressionResult($argExpr);
					if ($argResult === null) {
						return null;
					}
					if ($argResult->getTypeOnScope($evaluationScope, $evaluationScope->nativeTypesPromoted)->isString()->yes()) {
						return $this->defaultNarrowingHelper->createForSubject(
							$argExpr,
							new IntersectionType([new StringType(), new AccessoryNonEmptyStringType()]),
							$context->negate(),
							$evaluationScope,
						);
					}
				}
			}

			// other constants and contexts only pin the call
		}

		// a known parent class narrows the argument to the child side of it
		if (
			$unwrappedSubject instanceof Expr\FuncCall
			&& $unwrappedSubject->name->toLowerString() === 'get_parent_class'
		) {
			if ($context->true()) {
				$constantStrings = $constantType->getConstantStrings();
				if (count($constantStrings) === 1 && $constantStrings[0]->getValue() !== '') {
					$argExpr = $unwrappedSubject->getArgs()[0]->value;
					$argResult = $evaluationScope->getCurrentExpressionResultStorage()?->findExpressionResult($argExpr);
					if ($argResult === null) {
						return null;
					}
					$argType = $argResult->getTypeOnScope($evaluationScope, $evaluationScope->nativeTypesPromoted);
					$objectType = new ObjectType($constantStrings[0]->getValue());
					$classStringType = new GenericClassStringType($objectType);

					if ($argType->isString()->yes()) {
						$narrowed = $classStringType;
					} elseif ($argType->isObject()->yes()) {
						$narrowed = $objectType;
					} else {
						$narrowed = TypeCombinator::union($objectType, $classStringType);
					}

					return $this->defaultNarrowingHelper->createForSubject($argExpr, $narrowed, $context, $evaluationScope);
				}
			}

			return null;
		}

		// a string function whose result is a non-empty literal had a
		// non-empty (non-falsy for a non-falsy literal) string argument;
		// case-mapping functions pin the case accessory on the literal side
		if (
			$unwrappedSubject instanceof Expr\FuncCall
			&& in_array($unwrappedSubject->name->toLowerString(), [
				'substr', 'strstr', 'stristr', 'strchr', 'strrchr', 'strtolower', 'strtoupper', 'ucfirst', 'lcfirst',
				'mb_substr', 'mb_strstr', 'mb_stristr', 'mb_strchr', 'mb_strrchr', 'mb_strtolower', 'mb_strtoupper', 'mb_ucfirst', 'mb_lcfirst',
				'ucwords', 'mb_convert_case', 'mb_convert_kana',
			], true)
		) {
			if ($context->truthy() && $constantType->isNonEmptyString()->yes()) {
				$argExpr = $unwrappedSubject->getArgs()[0]->value;
				$argResult = $evaluationScope->getCurrentExpressionResultStorage()?->findExpressionResult($argExpr);
				if ($argResult === null) {
					return null;
				}
				$argType = $argResult->getTypeOnScope($evaluationScope, $evaluationScope->nativeTypesPromoted);

				if ($argType->isString()->yes()) {
					$types = new SpecifiedTypes();
					$funcName = $unwrappedSubject->name->toLowerString();
					if (in_array($funcName, ['strtolower', 'mb_strtolower'], true)) {
						$types = $this->defaultNarrowingHelper->createSubjectTypes($evaluationScope, $constantExpr, $constantResult, TypeCombinator::intersect($constantType, new AccessoryLowercaseStringType()), $context);
					} elseif (in_array($funcName, ['strtoupper', 'mb_strtoupper'], true)) {
						$types = $this->defaultNarrowingHelper->createSubjectTypes($evaluationScope, $constantExpr, $constantResult, TypeCombinator::intersect($constantType, new AccessoryUppercaseStringType()), $context);
					}

					$accessory = $constantType->isNonFalsyString()->yes()
						? new AccessoryNonFalsyStringType()
						: new AccessoryNonEmptyStringType();

					return $types->unionWith($this->defaultNarrowingHelper->createForSubject(
						$argExpr,
						TypeCombinator::intersect($argType, $accessory),
						$context,
						$evaluationScope,
					));
				}
			}

			// a non-string argument, an empty literal or a non-truthy
			// context only pins the call
		}

		// count($x) === N reconstructs the array shape by its size - before
		// the decided guard so exhaustive size switches keep collapsing
		if (
			$unwrappedSubject instanceof Expr\FuncCall
			&& in_array($unwrappedSubject->name->toLowerString(), ['count', 'sizeof'], true)
		) {
			if (!$constantType->isInteger()->yes()) {
				return null;
			}

			$argExpr = $unwrappedSubject->getArgs()[0]->value;
			$argResult = $evaluationScope->getCurrentExpressionResultStorage()?->findExpressionResult($argExpr);
			if ($argResult === null) {
				return null;
			}
			$argType = $argResult->getTypeOnScope($evaluationScope, $evaluationScope->nativeTypesPromoted);

			if ((new ConstantIntegerType(0))->isSuperTypeOf($constantType)->yes()) {
				$newArgType = $context->truthy() && !$argType->isArray()->yes()
					? new UnionType([new ObjectType(Countable::class), new ConstantArrayType([], [])])
					: new ConstantArrayType([], []);

				return $this->defaultNarrowingHelper->createSubjectTypes($evaluationScope, $subject, $subjectResult, $constantType, $context)->unionWith(
					$this->defaultNarrowingHelper->createForSubject($argExpr, $newArgType, $context, $evaluationScope),
				);
			}

			$countTypes = $this->countNarrowingHelper->specifyCountSize($unwrappedSubject, $argType, $constantType, $context, $evaluationScope, $unwrappedSubject);
			if ($countTypes !== null) {
				// the old path pinned the call only through the remembered
				// wrapper; the composed pin covers wrapper and call alike
				if ($subject !== $unwrappedSubject) {
					return $countTypes->unionWith($this->defaultNarrowingHelper->createSubjectTypes($evaluationScope, $subject, $subjectResult, $constantType, $context));
				}

				return $countTypes;
			}

			if ($context->truthy() && $argType->isArray()->yes()) {
				$types = $this->defaultNarrowingHelper->createSubjectTypes($evaluationScope, $subject, $subjectResult, $constantType, $context);
				if (IntegerRangeType::fromInterval(1, null)->isSuperTypeOf($constantType)->yes()) {
					return $types->unionWith(
						$this->defaultNarrowingHelper->createForSubject($argExpr, new NonEmptyArrayType(), $context, $evaluationScope),
					);
				}

				return $types;
			}

			// a non-array argument in a non-truthy context only pins the call
		}

		// strlen($x) === 0 empties $x; === N >= 1 makes it non-empty in the
		// truthy direction (>= 2 non-falsy) - before the decided guard
		if (
			$unwrappedSubject instanceof Expr\FuncCall
			&& in_array($unwrappedSubject->name->toLowerString(), ['strlen', 'mb_strlen'], true)
		) {
			if (count($unwrappedSubject->getArgs()) !== 1 || !$constantType->isInteger()->yes()) {
				return null;
			}

			$argExpr = $unwrappedSubject->getArgs()[0]->value;
			if ((new ConstantIntegerType(0))->isSuperTypeOf($constantType)->yes()) {
				return $this->defaultNarrowingHelper->createSubjectTypes($evaluationScope, $subject, $subjectResult, $constantType, $context)->unionWith(
					$this->defaultNarrowingHelper->createForSubject($argExpr, new ConstantStringType(''), $context, $evaluationScope),
				);
			}

			if ($context->truthy()) {
				$argResult = $evaluationScope->getCurrentExpressionResultStorage()?->findExpressionResult($argExpr);
				if ($argResult === null) {
					return null;
				}
				if ($argResult->getTypeOnScope($evaluationScope, $evaluationScope->nativeTypesPromoted)->isString()->yes()) {
					$accessory = IntegerRangeType::fromInterval(2, null)->isSuperTypeOf($constantType)->yes()
						? new AccessoryNonFalsyStringType()
						: new AccessoryNonEmptyStringType();

					return $this->defaultNarrowingHelper->createSubjectTypes($evaluationScope, $subject, $subjectResult, $constantType, $context)->unionWith(
						$this->defaultNarrowingHelper->createForSubject($argExpr, $accessory, $context, $evaluationScope),
					);
				}
			}

			// a non-string argument or a falsey non-zero size only pins the call
		}

		// gettype($x) === 'string' narrows $x by the named type in either
		// direction - before the decided-comparison guard, like the old block
		if (
			$unwrappedSubject instanceof Expr\FuncCall
			&& $unwrappedSubject->name->toLowerString() === 'gettype'
		) {
			$constantStrings = $constantType->getConstantStrings();
			if (count($constantStrings) !== 1) {
				return null;
			}
			$gettypeNarrowedType = $this->getTypeFromGettypeStringValue($constantStrings[0]->getValue());
			if ($gettypeNarrowedType !== null) {
				return $this->defaultNarrowingHelper->createSubjectTypes($evaluationScope, $subject, $subjectResult, $constantType, $context)->unionWith(
					$this->defaultNarrowingHelper->createForSubject($unwrappedSubject->getArgs()[0]->value, $gettypeNarrowedType, $context, $evaluationScope),
				);
			}
			// an unknown type-name string only pins the call itself below
		}

		$decidedTypes = $this->specifyDecidedComparison($left, $right, $leftResult, $rightResult, $context, $evaluationScope, $identicalTypeCallback);
		if ($decidedTypes !== null) {
			return $decidedTypes;
		}

		// get_class($o) === 'Foo' pins $o to a final Foo when the comparison
		// holds; outside the true context only the call itself narrows
		if ($unwrappedSubject instanceof Expr\FuncCall && $context->true()) {
			$narrowedObjectType = null;
			$constantStrings = $constantType->getConstantStrings();
			if (count($constantStrings) === 1 && $this->reflectionProvider->hasClass($constantStrings[0]->getValue())) {
				$narrowedObjectType = new ObjectType($constantStrings[0]->getValue(), classReflection: $this->reflectionProvider->getClass($constantStrings[0]->getValue())->asFinal());
			} elseif ($constantType->getClassStringObjectType()->isObject()->yes()) {
				$narrowedObjectType = $constantType->getClassStringObjectType();
			}

			if ($narrowedObjectType !== null) {
				return $this->defaultNarrowingHelper->createForSubject(
					$unwrappedSubject->getArgs()[0]->value,
					$narrowedObjectType,
					$context,
					$evaluationScope,
				)->unionWith($this->defaultNarrowingHelper->createSubjectTypes($evaluationScope, $subject, $subjectResult, $constantType, $context));
			}
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

	private function getTypeFromGettypeStringValue(string $value): ?Type
	{
		if ($value === 'string') {
			return new StringType();
		}
		if ($value === 'array') {
			return new ArrayType(new MixedType(), new MixedType());
		}
		if ($value === 'boolean') {
			return new BooleanType();
		}
		if (in_array($value, ['resource', 'resource (closed)'], true)) {
			return new ResourceType();
		}
		if ($value === 'integer') {
			return new IntegerType();
		}
		if ($value === 'double') {
			return new FloatType();
		}
		if ($value === 'NULL') {
			return new NullType();
		}
		if ($value === 'object') {
			return new ObjectWithoutClassType();
		}

		return null;
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
	 * calls narrow their arguments (count($a) === 0 empties $a), `$a::class`
	 * narrows $a. The null comparison is fully composed (the array_key_first
	 * family narrows its argument through the FuncCall's createTypesCallback)
	 * and does not consult this.
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
