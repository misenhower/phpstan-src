<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

use PhpParser\Node\Expr;
use PHPStan\DependencyInjection\GenerateFactory;
use PHPStan\DependencyInjection\Type\ExpressionTypeResolverExtensionRegistryProvider;
use PHPStan\Type\Type;
use PHPStan\Type\TypeUtils;

#[GenerateFactory(interface: ExpressionResultFactory::class)]
final class ExpressionResult
{

	/** @var (callable(MutatingScope, Expr): Type)|null */
	private $typeCallback;

	/** @var (callable(): MutatingScope)|null */
	private $truthyScopeCallback;

	private ?MutatingScope $truthyScope = null;

	/** @var (callable(): MutatingScope)|null */
	private $falseyScopeCallback;

	private ?MutatingScope $falseyScope = null;

	private ?Type $cachedType = null;

	private ?Type $cachedNativeType = null;

	/**
	 * @param InternalThrowPoint[] $throwPoints
	 * @param ImpurePoint[] $impurePoints
	 * @param (callable(MutatingScope, Expr): Type)|null $typeCallback
	 * @param (callable(): MutatingScope)|null $truthyScopeCallback
	 * @param (callable(): MutatingScope)|null $falseyScopeCallback
	 */
	public function __construct(
		private ExpressionTypeResolverExtensionRegistryProvider $expressionTypeResolverExtensionRegistryProvider,
		private MutatingScope $scope,
		private MutatingScope $beforeScope,
		private Expr $expr,
		private bool $hasYield,
		private bool $isAlwaysTerminating,
		private array $throwPoints,
		private array $impurePoints,
		?callable $truthyScopeCallback = null,
		?callable $falseyScopeCallback = null,
		?callable $typeCallback = null,
	)
	{
		$this->truthyScopeCallback = $truthyScopeCallback;
		$this->falseyScopeCallback = $falseyScopeCallback;
		$this->typeCallback = $typeCallback;
	}

	public function getScope(): MutatingScope
	{
		return $this->scope;
	}

	public function getBeforeScope(): MutatingScope
	{
		return $this->beforeScope;
	}

	public function hasYield(): bool
	{
		return $this->hasYield;
	}

	/**
	 * @return InternalThrowPoint[]
	 */
	public function getThrowPoints(): array
	{
		return $this->throwPoints;
	}

	/**
	 * @return ImpurePoint[]
	 */
	public function getImpurePoints(): array
	{
		return $this->impurePoints;
	}

	public function getTruthyScope(): MutatingScope
	{
		if ($this->truthyScope !== null) {
			return $this->truthyScope;
		}

		if ($this->truthyScopeCallback === null) {
			return $this->truthyScope = $this->scope->filterByTruthyValue($this->expr);
		}

		$callback = $this->truthyScopeCallback;
		return $this->truthyScope = $callback();
	}

	public function getFalseyScope(): MutatingScope
	{
		if ($this->falseyScope !== null) {
			return $this->falseyScope;
		}

		if ($this->falseyScopeCallback === null) {
			return $this->falseyScope = $this->scope->filterByFalseyValue($this->expr);
		}

		$callback = $this->falseyScopeCallback;
		return $this->falseyScope = $callback();
	}

	public function isAlwaysTerminating(): bool
	{
		return $this->isAlwaysTerminating;
	}

	public function getType(): Type
	{
		if ($this->cachedType !== null) {
			return $this->cachedType;
		}

		foreach ($this->expressionTypeResolverExtensionRegistryProvider->getRegistry()->getExtensions() as $extension) {
			$type = $extension->getType($this->expr, $this->beforeScope);
			if ($type !== null) {
				return $this->cachedType = $type;
			}
		}

		if ($this->typeCallback !== null) {
			return $this->cachedType = TypeUtils::resolveLateResolvableTypes(($this->typeCallback)($this->beforeScope, $this->expr));
		}

		return $this->cachedType = $this->beforeScope->getType($this->expr);
	}

	public function getNativeType(): Type
	{
		if ($this->cachedNativeType !== null) {
			return $this->cachedNativeType;
		}

		if ($this->typeCallback !== null) {
			return $this->cachedNativeType = TypeUtils::resolveLateResolvableTypes(($this->typeCallback)($this->beforeScope->doNotTreatPhpDocTypesAsCertain(), $this->expr));
		}

		return $this->cachedNativeType = $this->beforeScope->getNativeType($this->expr);
	}

}
