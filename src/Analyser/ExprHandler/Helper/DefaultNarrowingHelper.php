<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler\Helper;

use Closure;
use PhpParser\Node\Expr;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\Scope;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifier;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Printer\ExprPrinter;
use PHPStan\Type\StaticTypeFactory;
use PHPStan\Type\Type;

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
		private TypeSpecifier $typeSpecifier,
	)
	{
	}

	/**
	 * The narrowing of an already-processed child expression in the given
	 * boolean context: answered by the child result's specifyTypesCallback.
	 * When the child wired no callback, or is a synthetic node with no result,
	 * it is processed on demand and asked for its narrowing - the same path
	 * TypeSpecifier::specifyTypesInCondition() routes handler-supported nodes
	 * through, but without the old-world dispatcher.
	 */
	public function getChildSpecifiedTypes(MutatingScope $s, Expr $childExpr, ?ExpressionResult $childResult, TypeSpecifierContext $context): SpecifiedTypes
	{
		if ($childResult !== null) {
			$types = $childResult->getSpecifiedTypesForScope($s, $context);
			if ($types !== null) {
				return $types;
			}
		}

		return $this->specifyTypesForNode($s, $childExpr, $context);
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

		return $scope->toMutatingScope()->specifyTypesOfNewWorldHandlerNode($node, $context)
			?? $this->specifyDefaultTypes($node, $context);
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
	 * A greatly simplified TypeSpecifier::create() for a subject the calling
	 * handler has already processed: one sure (truthy) or sureNot (falsey)
	 * entry for the subject node. A coalesce subject narrows its left side
	 * when the narrowed type rules the right side in or out. No purity gates,
	 * no nullsafe chain-walking, no assignment fan-out - an entry about an
	 * assignment narrows the assigned variables in the appliers, and the
	 * subject's own narrowing composes in through
	 * ExpressionResult::getSpecifiedTypesForScope() at the call site.
	 */
	/**
	 * A greatly simplified TypeSpecifier::create() for a subject the calling
	 * handler has already processed: the subject's own result says how a type
	 * constraint on it translates into entries (an assignment fans out to the
	 * assigned variable, a coalesce delegates to its left side); without a
	 * createTypesCallback a single sure (truthy) or sureNot (falsey) entry
	 * for the subject node is emitted. No purity gates, no nullsafe
	 * chain-walking, no structural unwrapping - the handlers that own those
	 * nodes compose their children's results inside-out.
	 */
	public function createSubjectTypes(MutatingScope $s, Expr $subject, ?ExpressionResult $subjectResult, Type $type, TypeSpecifierContext $context): SpecifiedTypes
	{
		if ($subjectResult !== null) {
			$createdTypes = $subjectResult->getCreatedTypesForScope($s, $type, $context);
			if ($createdTypes !== null) {
				return $createdTypes;
			}
		}

		// No composable result (a synthetic node, or a subject whose handler wired
		// no createTypesCallback): fall back to the raw-Expr create(), which does the
		// structural fan-out (assignment / remembered wrapper) and createForExpr. For
		// a plain subject this equals the single sure/sureNot entry it used to emit.
		return $this->typeSpecifier->create($subject, $type, $context, $s);
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

}
