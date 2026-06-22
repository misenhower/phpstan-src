<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

use PhpParser\Node\Expr;
use PHPStan\DependencyInjection\GenerateFactory;
use PHPStan\DependencyInjection\Type\ExpressionTypeResolverExtensionRegistryProvider;
use PHPStan\ShouldNotHappenException;
use PHPStan\Type\Type;
use PHPStan\Type\TypeUtils;
use function array_key_exists;

#[GenerateFactory(interface: ExpressionResultFactory::class)]
final class ExpressionResult
{

	/** @var (callable(MutatingScope, Expr): Type)|null */
	private $typeCallback;

	/** @var (callable(MutatingScope, TypeSpecifierContext): SpecifiedTypes)|null */
	private $specifyTypesCallback;

	/** @var (callable(MutatingScope, Type, TypeSpecifierContext): SpecifiedTypes)|null */
	private $createTypesCallback;

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
	 * @param (callable(MutatingScope, TypeSpecifierContext): SpecifiedTypes)|null $specifyTypesCallback
	 * @param (callable(MutatingScope, Type, TypeSpecifierContext): SpecifiedTypes)|null $createTypesCallback
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
		private bool $containsNullsafe = false,
		private ?IssetabilityDescriptor $issetabilityDescriptor = null,
		?callable $truthyScopeCallback = null,
		?callable $falseyScopeCallback = null,
		?callable $typeCallback = null,
		?callable $specifyTypesCallback = null,
		?callable $createTypesCallback = null,
		private ?Type $type = null,
		private ?Type $nativeType = null,
	)
	{
		$this->truthyScopeCallback = $truthyScopeCallback;
		$this->falseyScopeCallback = $falseyScopeCallback;
		$this->typeCallback = $typeCallback;
		$this->specifyTypesCallback = $specifyTypesCallback;
		$this->createTypesCallback = $createTypesCallback;
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
	 * Whether this expression's chain contains a nullsafe operator (?->). A
	 * fetch/call on a receiver whose chain short-circuits propagates null,
	 * which a plain nullable receiver (e.g. a nullable variable) does not -
	 * this flag is what tells them apart.
	 */
	public function containsNullsafe(): bool
	{
		return $this->containsNullsafe;
	}

	/**
	 * The fully-resolved isset/empty/?? view of this expression on the asking
	 * scope: folds the chain descriptor, or builds a leaf resolution from the
	 * expression's own type when it is not a chain link (e.g. a method-call-rooted
	 * base like $this->getFoo()['x']). $useNativeTypes selects native vs phpdoc.
	 */
	public function getIssetabilityResolution(MutatingScope $scope, bool $useNativeTypes): IssetabilityResolution
	{
		if ($this->issetabilityDescriptor !== null) {
			return $this->issetabilityDescriptor->resolve($scope, $useNativeTypes, $this->expr);
		}

		$type = $useNativeTypes ? $this->getNativeTypeForScope($scope) : $this->getTypeForScope($scope);

		return new IssetabilityResolution(
			IssetabilityLinkInfo::leaf($type, $this->expr, $this->expr instanceof Expr\NullsafePropertyFetch),
			null,
		);
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
			if ($this->specifyTypesCallback !== null) {
				return $this->truthyScope = $this->scope->applySpecifiedTypes(
					($this->specifyTypesCallback)($this->scope, TypeSpecifierContext::createTruthy()),
				);
			}

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
			if ($this->specifyTypesCallback !== null) {
				return $this->falseyScope = $this->scope->applySpecifiedTypes(
					($this->specifyTypesCallback)($this->scope, TypeSpecifierContext::createFalsey()),
				);
			}

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
		if ($this->type !== null) {
			return $this->type;
		}

		if ($this->cachedType !== null) {
			return $this->cachedType;
		}

		foreach ($this->expressionTypeResolverExtensionRegistryProvider->getRegistry()->getExtensions() as $extension) {
			$type = $extension->getType($this->expr, $this->beforeScope);
			if ($type !== null) {
				return $this->cachedType = $type;
			}
		}

		if ($this->hasTrackedExpressionType($this->beforeScope)) {
			return $this->cachedType = $this->getTrackedExpressionType($this->beforeScope);
		}

		if ($this->typeCallback !== null) {
			return $this->cachedType = TypeUtils::resolveLateResolvableTypes(($this->typeCallback)($this->beforeScope, $this->expr));
		}

		throw new ShouldNotHappenException('Unknown type');
	}

	public function getNativeType(): Type
	{
		if ($this->nativeType !== null) {
			return $this->nativeType;
		}

		if ($this->cachedNativeType !== null) {
			return $this->cachedNativeType;
		}

		if ($this->hasTrackedExpressionNativeType($this->beforeScope)) {
			return $this->cachedNativeType = $this->getTrackedExpressionNativeType($this->beforeScope);
		}

		if ($this->typeCallback !== null) {
			return $this->cachedNativeType = TypeUtils::resolveLateResolvableTypes(($this->typeCallback)($this->beforeScope->doNotTreatPhpDocTypesAsCertain(), $this->expr));
		}

		throw new ShouldNotHappenException('Unkown native type');
	}

	/**
	 * A narrowed or ensured type tracked for the whole expression (e.g. the
	 * nullsafe handlers ensure `($x ?? null)` is not null before processing
	 * the chain) wins over recomputing the type - mirrors the tracked-holder
	 * early return in MutatingScope::resolveType(). Asking the scope is safe:
	 * its own early return answers from the holder without dispatching back.
	 */
	private function hasTrackedExpressionType(MutatingScope $scope): bool
	{
		return !$this->expr instanceof Expr\Closure
			&& !$this->expr instanceof Expr\ArrowFunction
			&& array_key_exists($scope->getNodeKey($this->expr), $scope->expressionTypes);
	}

	private function getTrackedExpressionType(MutatingScope $scope): Type
	{
		// Match the typeCallback branches (and MutatingScope::getType): the stored
		// holder may carry an unresolved ConditionalType from a @phpstan-assert, so
		// resolve late-resolvable types here too (no-op when there are none).
		return TypeUtils::resolveLateResolvableTypes($scope->expressionTypes[$scope->getNodeKey($this->expr)]->getType());
	}

	private function hasTrackedExpressionNativeType(MutatingScope $scope): bool
	{
		return !$this->expr instanceof Expr\Closure
			&& !$this->expr instanceof Expr\ArrowFunction
			&& array_key_exists($scope->getNodeKey($this->expr), $scope->nativeExpressionTypes);
	}

	private function getTrackedExpressionNativeType(MutatingScope $scope): Type
	{
		return TypeUtils::resolveLateResolvableTypes($scope->nativeExpressionTypes[$scope->getNodeKey($this->expr)]->getType());
	}

	/**
	 * Whether this result can answer its own type without asking the scope -
	 * either an eagerly computed value (e.g. a closure's ClosureType) or a
	 * typeCallback. The new-world resolution in MutatingScope gates on this.
	 */
	public function canResolveOwnType(): bool
	{
		return $this->type !== null || $this->typeCallback !== null;
	}

	/**
	 * Re-evaluates the narrowing on a different scope (e.g. the one an old-world
	 * caller holds). Returns null when the handler wired no specifyTypesCallback -
	 * the caller falls back to default truthy/falsey narrowing.
	 */
	public function getSpecifiedTypesForScope(MutatingScope $scope, TypeSpecifierContext $context): ?SpecifiedTypes
	{
		if ($this->specifyTypesCallback === null) {
			return null;
		}

		return ($this->specifyTypesCallback)($scope, $context);
	}

	/**
	 * How a type constraint on this expression translates into narrowing
	 * entries - the inside-out counterpart of TypeSpecifier::create(). The
	 * handler that produced this result knows the structure: an assignment
	 * fans out to the assigned variable and the assigned expression
	 * (recursing through the assigned expression's own result), a coalesce
	 * delegates to its left side when the type rules the right side in or
	 * out. Returns null when the handler wired no createTypesCallback - the
	 * caller emits a single entry for the expression itself.
	 */
	public function getCreatedTypesForScope(MutatingScope $scope, Type $type, TypeSpecifierContext $context): ?SpecifiedTypes
	{
		if ($this->createTypesCallback === null) {
			return null;
		}

		return ($this->createTypesCallback)($scope, $type, $context);
	}

	/**
	 * Re-evaluates the expression type on a different scope (e.g. a narrowed one).
	 * Unlike getType(), the result is not cached.
	 */
	public function getTypeForScope(MutatingScope $scope): Type
	{
		// A native-promoted scope asks getType() but means the native flavour
		// (MutatingScope::getNativeType() promotes then calls getType()); the
		// eager value is stored as a (phpdoc, native) pair, so honour the scope.
		if ($this->nativeType !== null && $scope->nativeTypesPromoted) {
			return $this->nativeType;
		}

		if ($this->type !== null) {
			return $this->type;
		}

		if ($this->hasTrackedExpressionType($this->beforeScope)) {
			return $this->getTrackedExpressionType($this->beforeScope);
		}

		if ($this->typeCallback !== null) {
			return TypeUtils::resolveLateResolvableTypes(($this->typeCallback)($scope, $this->expr));
		}

		throw new ShouldNotHappenException('Unknown type for scope');
	}

	/** Native counterpart of getTypeForScope(). */
	public function getNativeTypeForScope(MutatingScope $scope): Type
	{
		if ($this->nativeType !== null) {
			return $this->nativeType;
		}

		if ($this->hasTrackedExpressionNativeType($this->beforeScope)) {
			return $this->getTrackedExpressionNativeType($this->beforeScope);
		}

		if ($this->typeCallback !== null) {
			return TypeUtils::resolveLateResolvableTypes(($this->typeCallback)($scope->doNotTreatPhpDocTypesAsCertain(), $this->expr));
		}

		throw new ShouldNotHappenException('Unknown native type for scope');
	}

}
