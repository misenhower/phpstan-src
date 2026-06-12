<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

use Fiber;
use PhpParser\Node;
use PhpParser\Node\Expr;
use PHPStan\Analyser\Fiber\ExpressionResultRequest;
use PHPStan\Analyser\Fiber\ParkFiberRequest;
use SplObjectStorage;

final class ExpressionResultStorage
{

	/** @var SplObjectStorage<Expr, ExpressionResult> */
	private SplObjectStorage $exprResults;

	/** @var array<array{fiber: Fiber<mixed, ExpressionResult|array{callable(Node $node, Scope $scope): void, Node, MutatingScope}, null, ExpressionResultRequest|ParkFiberRequest>, request: ExpressionResultRequest}> */
	public array $pendingFibers = [];

	/** @var list<Fiber<mixed, ExpressionResult|array{callable(Node $node, Scope $scope): void, Node, MutatingScope}, null, ExpressionResultRequest|ParkFiberRequest>> */
	public array $parkedFibers = [];

	public function __construct()
	{
		$this->exprResults = new SplObjectStorage();
	}

	public function duplicate(): self
	{
		$new = new self();
		$new->exprResults->addAll($this->exprResults);
		return $new;
	}

	public function mergeResults(self $other): void
	{
		$this->exprResults->addAll($other->exprResults);
	}

	public function storeExpressionResult(Expr $expr, ExpressionResult $expressionResult): void
	{
		$this->exprResults[$expr] = $expressionResult;
	}

	public function findExpressionResult(Expr $expr): ?ExpressionResult
	{
		return $this->exprResults[$expr] ?? null;
	}

}
