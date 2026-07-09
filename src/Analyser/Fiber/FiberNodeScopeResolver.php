<?php declare(strict_types = 1);

namespace PHPStan\Analyser\Fiber;

use Fiber;
use PhpParser\Node;
use PhpParser\Node\Expr;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\GatheringNodeCallback;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\ReadVariableStateSnapshot;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\NoopNodeCallback;
use PHPStan\Analyser\Scope;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\ShouldNotHappenException;
use PHPStan\Type\Type;
use WeakMap;
use function array_pop;
use function count;
use function get_class;
use function get_debug_type;
use function spl_object_id;
use function sprintf;

#[AutowiredService(as: FiberNodeScopeResolver::class)]
final class FiberNodeScopeResolver extends NodeScopeResolver
{

	/**
	 * Last flush-priced answer per asked expression - see processPendingFibers().
	 *
	 * @var WeakMap<Expr, array{ReadVariableStateSnapshot, Type, Type}>|null
	 */
	private ?WeakMap $flushedOnDemandResults = null;

	/**
	 * @param callable(Node $node, Scope $scope): void $nodeCallback
	 */
	public function callNodeCallback(
		callable $nodeCallback,
		Node $node,
		MutatingScope $scope,
		ExpressionResultStorage $storage,
	): void
	{
		// Engine-feeding gatherers must observe the node at the emission
		// position - their arrays are read as soon as the enclosing body walk
		// returns. Only the rule-facing remainder may be deferred to a fiber;
		// a rule parking on an unsettled expression must not delay gathering.
		while ($nodeCallback instanceof GatheringNodeCallback) {
			($nodeCallback->getGatherer())($node, $scope->toFiberScope());
			$nodeCallback = $nodeCallback->getInner();
		}

		if ($nodeCallback instanceof NoopNodeCallback) {
			// fibers exist solely to let node callbacks ask about types,
			// a noop callback does not need one
			return;
		}

		if (Fiber::getCurrent() !== null) {
			$nodeCallback($node, $scope->toFiberScope());
			return;
		}
		if (count($storage->parkedFibers) > 0) {
			$fiber = array_pop($storage->parkedFibers);
			$request = $fiber->resume([$nodeCallback, $node, $scope]);
		} else {
			$fiber = new Fiber(static function () use ($node, $scope, $nodeCallback) {
				while (true) { // @phpstan-ignore while.alwaysTrue
					$nodeCallback($node, $scope->toFiberScope());
					[$nodeCallback, $node, $scope] = Fiber::suspend(new ParkFiberRequest());
				}
			});
			$request = $fiber->start();
		}
		$this->runFiberForNodeCallback($storage, $fiber, $request);
	}

	public function storeExpressionResult(ExpressionResultStorage $storage, Expr $expr, ExpressionResult $expressionResult): void
	{
		parent::storeExpressionResult($storage, $expr, $expressionResult);
		$this->processPendingFibersForRequestedExpr($storage, $expr, $expressionResult);
	}

	/**
	 * @param Fiber<mixed, ExpressionResult|array{callable(Node $node, Scope $scope): void, Node, MutatingScope}, null, ExpressionResultRequest|ParkFiberRequest> $fiber
	 */
	private function runFiberForNodeCallback(
		ExpressionResultStorage $storage,
		Fiber $fiber,
		ExpressionResultRequest|ParkFiberRequest|null $request,
	): void
	{
		while (!$fiber->isTerminated()) {
			if ($request instanceof ExpressionResultRequest) {
				$expressionResult = $this->findSettledExpressionResult($storage, $request->expr);
				if ($expressionResult !== null) {
					$request = $fiber->resume($expressionResult);
					continue;
				}

				$storage->pendingFibers[] = [
					'fiber' => $fiber,
					'request' => $request,
				];
				return;
			}
			if ($request instanceof ParkFiberRequest) {
				$storage->parkedFibers[] = $fiber;
				return;
			}

			throw new ShouldNotHappenException(
				'Unknown fiber suspension: ' . get_debug_type($request),
			);
		}

		if ($request !== null) {
			throw new ShouldNotHappenException(
				'Fiber terminated but we did not handle its request ' . get_debug_type($request),
			);
		}
	}

	protected function processPendingFibers(ExpressionResultStorage $storage): void
	{
		start:

		foreach ($storage->pendingFibers as $key => $pending) {
			$request = $pending['request'];

			// A fiber suspended on an expression that is still being processed
			// must not be flushed here: this boundary is a nested statement list
			// inside that very expression (e.g. an immediately-invoked closure's
			// body). The fiber is resumed when the enclosing processExprNode
			// stores the result.
			if (isset($this->processingExprIds[spl_object_id($request->expr)])) {
				continue;
			}

			$expressionResult = $storage->findExpressionResult($request->expr);

			if ($expressionResult !== null) {
				throw new ShouldNotHappenException('Pending fibers at the end should be about synthetic nodes');
			}

			// Only nodes built during analysis (rules constructing synthetic
			// comparisons, ArgumentsNormalizer rewrites, ...) should reach the
			// on-demand path here. A node from the file's parsed AST left pending
			// means a rule asked about its type but it was never processed and
			// stored during natural traversal - a gap to fix at the producing
			// handler. A node that WAS stored but whose per-body storage has been
			// released since (class-level rules asking about gathered method-body
			// exprs) is fine - the on-demand re-price below is the rule-facing
			// bridge for those, same as in the other guards' processed check.
			// Guard kept dormant; enable with PHPSTAN_GUARD_NW=1.
			if (
				self::$guardNewWorld
				&& isset(self::$guardRealExprIds[spl_object_id($request->expr)])
				&& !isset(self::$guardProcessedExprIds[spl_object_id($request->expr)])
			) {
				throw new ShouldNotHappenException(sprintf(
					'Pending fiber about real AST node %s on line %d - it should have been processed and its result stored during natural traversal.',
					get_class($request->expr),
					$request->expr->getStartLine(),
				));
			}

			unset($storage->pendingFibers[$key]);

			$fiber = $pending['fiber'];

			// Rules ask about the same (usually synthetic) node repeatedly across
			// statement boundaries; the answer is reusable whenever nothing the
			// expression reads changed since the walk. Only the state snapshot
			// and the materialized types are retained - keeping the walk result
			// would pin its scope and callback graphs for every parser-cached
			// file. The hit is fabricated at the ask position, exactly where a
			// fresh walk's result would sit.
			$askScope = $request->scope->toMutatingScope();
			$this->flushedOnDemandResults ??= new WeakMap();
			$memoEntry = $this->flushedOnDemandResults[$request->expr] ?? null;
			if ($memoEntry !== null && $memoEntry[0]->matches($askScope)) {
				$expressionResult = $this->createEagerExpressionResult($askScope, $request->expr, $memoEntry[1], $memoEntry[2]);
			} else {
				// Process the node with a duplicated storage so that the result
				// computed from the asker's scope does not poison the real storage.
				$expressionResult = $this->processExprOnDemand(
					$request->expr,
					$askScope,
					$storage->duplicate(),
				);
				$this->flushedOnDemandResults[$request->expr] = [
					$expressionResult->takeReadVariableStateSnapshot(),
					$expressionResult->getType(),
					$expressionResult->getNativeType(),
				];
			}
			$request = $fiber->resume($expressionResult);
			$this->runFiberForNodeCallback($storage, $fiber, $request);

			// Break and restart the loop since the array may have been modified
			goto start;
		}
	}

	private function processPendingFibersForRequestedExpr(ExpressionResultStorage $storage, Expr $expr, ExpressionResult $expressionResult): void
	{
		start:

		foreach ($storage->pendingFibers as $key => $pending) {
			$request = $pending['request'];
			if ($request->expr !== $expr) {
				continue;
			}

			unset($storage->pendingFibers[$key]);

			$fiber = $pending['fiber'];
			$request = $fiber->resume($expressionResult);
			$this->runFiberForNodeCallback($storage, $fiber, $request);

			// Break and restart the loop since the array may have been modified
			goto start;
		}
	}

}
