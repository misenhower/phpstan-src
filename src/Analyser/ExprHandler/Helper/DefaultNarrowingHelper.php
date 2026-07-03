<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use Closure;
use PhpParser\Node\Expr;
use PhpParser\Node\Expr\ArrayDimFetch;
use PhpParser\Node\Expr\PropertyFetch;
use PhpParser\Node\Expr\StaticPropertyFetch;
use PhpParser\Node\Identifier;
use PhpParser\Node\VarLikeIdentifier;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NullsafeOperatorHelper;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\Scope;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredParameter;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Printer\ExprPrinter;
use PHPStan\Rules\Arrays\AllowedArrayKeysTypes;
use PHPStan\Type\Accessory\HasOffsetType;
use PHPStan\Type\Accessory\HasPropertyType;
use PHPStan\Type\Accessory\NonEmptyArrayType;
use PHPStan\Type\Constant\ConstantIntegerType;
use PHPStan\Type\Constant\ConstantStringType;
use PHPStan\Type\IntersectionType;
use PHPStan\Type\MixedType;
use PHPStan\Type\NullType;
use PHPStan\Type\ObjectWithoutClassType;
use PHPStan\Type\StaticTypeFactory;
use PHPStan\Type\TypeCombinator;
use PHPStan\Type\Type;
use function array_reverse;
use function is_string;
use function spl_object_id;

/**
 * New-world replacement for TypeSpecifier::handleDefaultTruthyOrFalseyContext():
 * the default narrowing of an expression used in a boolean context.
 *
 * Unlike the old world there is no nullsafe short-circuiting here: expressions
 * process inside-out, so only the nullsafe handlers ever see a `?->` - they
 * emit the plain-chain variant alongside their own key once, and every parent
 * simply composes their results. No recursive chain-walking, no type ask.
 */
#[AutowiredService]
final class DefaultNarrowingHelper
{

	public function __construct(
		private ExprPrinter $exprPrinter,
		#[AutowiredParameter]
		private bool $rememberPossiblyImpureFunctionValues,
	)
	{
	}

	/**
	 * Narrows an arbitrary (often synthetic) node in the given boolean context by
	 * processing it on demand and asking its result, the inside-out replacement
	 * for TypeSpecifier::specifyTypesInCondition() on the handler path. A node not
	 * stored is processed on demand; a node whose handler wired no specifyTypesCallback
	 * (or no handler) yields the default truthy/falsey narrowing.
	 */
	public function specifyTypesForNode(Scope $scope, Expr $node, TypeSpecifierContext $context): SpecifiedTypes
	{
		if ($node instanceof Expr\CallLike && $node->isFirstClassCallable()) {
			return (new SpecifiedTypes([], []))->setRootExpr($node);
		}

		return $scope->toMutatingScope()->specifyTypesOfNewWorldHandlerNode($node, $context);
	}

	public function specifyDefaultTypes(Expr $expr, TypeSpecifierContext $context): SpecifiedTypes
	{
		if ($context->null()) {
			return (new SpecifiedTypes([], []))->setRootExpr($expr);
		}

		if (!$context->truthy()) {
			$removedType = StaticTypeFactory::truthy();
		} elseif (!$context->falsey()) {
			$removedType = StaticTypeFactory::falsey();
		} else {
			return (new SpecifiedTypes([], []))->setRootExpr($expr);
		}

		return (new SpecifiedTypes(sureNotTypes: [
			$this->exprPrinter->printExpr($expr) => [$expr, $removedType],
		]))->setRootExpr($expr);
	}

	/**
	 * The new-world counterpart of TypeSpecifier::create() for a subject the
	 * calling handler has already processed. The subject's own result says how
	 * a type constraint on it translates into entries (an assignment fans out
	 * to the assigned variable, a coalesce delegates to its left side); without
	 * a createTypesCallback the entries are composed here from the result's own
	 * facts: a call whose execution is (possibly) impure gets none, a chain
	 * containing a nullsafe additionally narrows its short-circuited plain twin.
	 * TypeSpecifier::create()/createForExpr() are never reached - their
	 * old-world machinery re-derives from the scope what the result already
	 * carries.
	 */
	public function createSubjectTypes(MutatingScope $s, Expr $subject, ?ExpressionResult $subjectResult, Type $type, TypeSpecifierContext $context): SpecifiedTypes
	{
		if ($subjectResult !== null) {
			$createdTypes = $subjectResult->getCreatedTypesForScope($s, $type, $context);
			if ($createdTypes !== null) {
				return $createdTypes;
			}
		}

		if ($subject instanceof Expr\Instanceof_ || $subject instanceof Expr\List_) {
			return new SpecifiedTypes([], []);
		}

		$exprToSpecify = $subject;
		if ($subjectResult !== null) {
			// a call whose own execution is (possibly) impure must not get a
			// remembered type - the gate reads the result's own impure point
			// instead of re-asking reflection like the old create() did
			if (
				$subject instanceof Expr\FuncCall
				|| $subject instanceof Expr\MethodCall
				|| $subject instanceof Expr\StaticCall
				|| $subject instanceof Expr\NullsafeMethodCall
			) {
				foreach ($subjectResult->getImpurePoints() as $impurePoint) {
					if ($impurePoint->getNode() !== $subject) {
						continue;
					}
					if ($impurePoint->isCertain() || !$this->rememberPossiblyImpureFunctionValues) {
						return new SpecifiedTypes([], []);
					}

					break;
				}
			}

			// a chain containing a nullsafe narrows its short-circuited plain
			// twin too, when the constraint (or the subject's own type) rules
			// the short-circuit null out - the containsNullsafe flag and the
			// memoized result type replace the old scope-type probe
			if ($subjectResult->containsNullsafe()) {
				if ($context->true()) {
					$nullRuledOut = $type->isNull()->no() || $subjectResult->getTypeOnScope($s, $s->nativeTypesPromoted)->isNull()->no();
				} elseif ($context->false()) {
					$nullRuledOut = TypeCombinator::containsNull($type) || $subjectResult->getTypeOnScope($s, $s->nativeTypesPromoted)->isNull()->no();
				} else {
					$nullRuledOut = false;
				}

				if ($nullRuledOut) {
					$exprToSpecify = NullsafeOperatorHelper::getNullsafeShortcircuitedExpr($subject);
				}
			}
		}

		$sureTypes = [];
		$sureNotTypes = [];
		if ($context->false()) {
			$sureNotTypes[$this->exprPrinter->printExpr($exprToSpecify)] = [$exprToSpecify, $type];
			if ($exprToSpecify !== $subject) {
				$sureNotTypes[$this->exprPrinter->printExpr($subject)] = [$subject, $type];
			}
		} elseif ($context->true()) {
			$sureTypes[$this->exprPrinter->printExpr($exprToSpecify)] = [$exprToSpecify, $type];
			if ($exprToSpecify !== $subject) {
				$sureTypes[$this->exprPrinter->printExpr($subject)] = [$subject, $type];
			}
		}

		return new SpecifiedTypes($sureTypes, $sureNotTypes);
	}

	/**
	 * The inside-out create() for a raw subject: narrows it through its own stored
	 * result's createTypesCallback, falling back to create() when there is none.
	 * When the caller already holds the subject's result (e.g. an operand a parent
	 * handler just processed) it passes a $resultFor lookup so composition uses that
	 * captured result directly instead of a storage lookup - so a remembered-wrapper
	 * operand fans out to wrapper + inner without the caller unwrapping it.
	 *
	 * @param (Closure(Expr): ?ExpressionResult)|null $resultFor
	 */
	public function createForSubject(Expr $subject, Type $type, TypeSpecifierContext $context, Scope $scope, ?Closure $resultFor = null): SpecifiedTypes
	{
		$mutatingScope = $scope->toMutatingScope();
		$subjectResult = $resultFor !== null ? $resultFor($subject) : null;

		return $this->createSubjectTypes(
			$mutatingScope,
			$subject,
			$subjectResult ?? $mutatingScope->getCurrentExpressionResultStorage()?->findExpressionResult($subject),
			$type,
			$context,
		);
	}


	/**
	 * Captures the stored ExpressionResults of an isset/empty/?? subject's
	 * chain links (the results, not the storage - no reference cycle) so
	 * narrowing callbacks read their types instead of re-walking the chain.
	 *
	 * @param array<int, ExpressionResult> $chainResults
	 */
	public function captureChainResults(Expr $node, ExpressionResultStorage $storage, array &$chainResults): void
	{
		$result = $storage->findExpressionResult($node);
		if ($result !== null) {
			$chainResults[spl_object_id($node)] = $result;
		}

		if ($node instanceof ArrayDimFetch) {
			$this->captureChainResults($node->var, $storage, $chainResults);
			if ($node->dim !== null) {
				$this->captureChainResults($node->dim, $storage, $chainResults);
			}
		} elseif ($node instanceof PropertyFetch) {
			$this->captureChainResults($node->var, $storage, $chainResults);
		} elseif ($node instanceof StaticPropertyFetch && $node->class instanceof Expr) {
			$this->captureChainResults($node->class, $storage, $chainResults);
		}
	}

	/**
	 * The chain-link type reader for the captured results: an already-processed
	 * link resolves through its result on the asking scope (honouring narrowing),
	 * anything else through the maybe-stored fallback.
	 *
	 * @param array<int, ExpressionResult> $chainResults
	 * @return Closure(Expr): Type
	 */
	public function buildChainTypeReader(array $chainResults, MutatingScope $s, NodeScopeResolver $nodeScopeResolver): Closure
	{
		return static function (Expr $e) use ($chainResults, $s, $nodeScopeResolver): Type {
			$result = $chainResults[spl_object_id($e)] ?? null;

			return $result !== null ? $result->getTypeOnScope($s, $s->nativeTypesPromoted) : $nodeScopeResolver->readTypeOfMaybeStored($e, $s);
		};
	}

	/**
	 * The truthy narrowing of isset($issetExpr), composed from the subject's
	 * chain: per-link HasOffset/NonEmptyArray/HasProperty facts plus a not-null
	 * entry for every link - exactly what the Isset_ handler emits in the true
	 * context. Lets ?? narrow its left side without synthesizing an Isset_ node
	 * and re-walking the chain on demand.
	 *
	 * @param Closure(Expr): Type $readType
	 */
	public function createIssetTruthyChainTypes(MutatingScope $s, Expr $issetExpr, Closure $readType, Expr $rootExpr, TypeSpecifierContext $context): SpecifiedTypes
	{
		$tmpVars = [$issetExpr];
		while (
			$issetExpr instanceof ArrayDimFetch
			|| $issetExpr instanceof PropertyFetch
			|| (
				$issetExpr instanceof StaticPropertyFetch
				&& $issetExpr->class instanceof Expr
			)
		) {
			if ($issetExpr instanceof StaticPropertyFetch) {
				/** @var Expr $issetExpr */
				$issetExpr = $issetExpr->class;
			} else {
				$issetExpr = $issetExpr->var;
			}
			$tmpVars[] = $issetExpr;
		}
		$vars = array_reverse($tmpVars);

		$types = new SpecifiedTypes();
		foreach ($vars as $var) {

			if ($var instanceof Expr\Variable && is_string($var->name)) {
				if ($s->hasVariableType($var->name)->no()) {
					return (new SpecifiedTypes([], []))->setRootExpr($rootExpr);
				}
			}

			if (
				$var instanceof ArrayDimFetch
				&& $var->dim !== null
				&& !$readType($var->var) instanceof MixedType
			) {
				$dimType = $readType($var->dim);

				if ($dimType instanceof ConstantIntegerType || $dimType instanceof ConstantStringType) {
					$types = $types->unionWith(
						$this->createForSubject(
							$var->var,
							new HasOffsetType($dimType),
							$context,
							$s,
						)->setRootExpr($rootExpr),
					);
				} else {
					$varType = $readType($var->var);

					$narrowedKey = AllowedArrayKeysTypes::narrowOffsetKeyType($varType, $dimType);
					if ($narrowedKey !== null) {
						$types = $types->unionWith(
							$this->createForSubject(
								$var->dim,
								$narrowedKey,
								$context,
								$s,
							)->setRootExpr($rootExpr),
						);
					}

					if ($varType->isArray()->yes()) {
						$types = $types->unionWith(
							$this->createForSubject(
								$var->var,
								new NonEmptyArrayType(),
								$context,
								$s,
							)->setRootExpr($rootExpr),
						);
					}
				}
			}

			if (
				$var instanceof PropertyFetch
				&& $var->name instanceof Identifier
			) {
				$types = $types->unionWith(
					$this->createForSubject($var->var, new IntersectionType([
						new ObjectWithoutClassType(),
						new HasPropertyType($var->name->toString()),
					]), TypeSpecifierContext::createTruthy(), $s)->setRootExpr($rootExpr),
				);
			} elseif (
				$var instanceof StaticPropertyFetch
				&& $var->class instanceof Expr
				&& $var->name instanceof VarLikeIdentifier
			) {
				$types = $types->unionWith(
					$this->createForSubject($var->class, new IntersectionType([
						new ObjectWithoutClassType(),
						new HasPropertyType($var->name->toString()),
					]), TypeSpecifierContext::createTruthy(), $s)->setRootExpr($rootExpr),
				);
			}

			$types = $types->unionWith(
				$this->createForSubject($var, new NullType(), TypeSpecifierContext::createFalse(), $s)->setRootExpr($rootExpr),
			);
		}

		return $types;
	}

}
