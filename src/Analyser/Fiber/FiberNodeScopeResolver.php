<?php declare(strict_types = 1);

namespace PHPStan\Analyser\Fiber;

use Fiber;
use PhpParser\Node;
use PhpParser\Node\Expr;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\NoopNodeCallback;
use PHPStan\Analyser\Scope;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\ShouldNotHappenException;
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
	 * @param callable(Node $node, Scope $scope): void $nodeCallback
	 */
	public function callNodeCallback(
		callable $nodeCallback,
		Node $node,
		MutatingScope $scope,
		ExpressionResultStorage $storage,
	): void
	{
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
				// a provisional pre-store is not an answer for outside askers -
				// park until the handler stores the final result
				$expressionResult = isset($this->provisionalExprIds[spl_object_id($request->expr)])
					? null
					: $storage->findExpressionResult($request->expr);
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
			// handler. Guard kept dormant; enable with PHPSTAN_GUARD_NW=1.
			if (self::$guardNewWorld && isset(self::$guardRealExprIds[spl_object_id($request->expr)])) {
				throw new ShouldNotHappenException(sprintf(
					'Pending fiber about real AST node %s on line %d - it should have been processed and its result stored during natural traversal.',
					get_class($request->expr),
					$request->expr->getStartLine(),
				));
			}

			unset($storage->pendingFibers[$key]);

			$fiber = $pending['fiber'];

			// Process the synthetic node with a duplicated storage so that the result
			// computed from the asker's scope does not poison the real storage.
			$expressionResult = $this->processExprOnDemand(
				$request->expr,
				$request->scope->toMutatingScope(),
				$storage->duplicate(),
			);
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
