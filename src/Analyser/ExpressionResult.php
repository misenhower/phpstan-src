<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

use PhpParser\Node\Expr;
use PHPStan\DependencyInjection\GenerateFactory;
use PHPStan\DependencyInjection\Type\ExpressionTypeResolverExtensionRegistryProvider;
use PHPStan\ShouldNotHappenException;
use PHPStan\Type\Type;
use PHPStan\Type\TypeUtils;

#[GenerateFactory(interface: ExpressionResultFactory::class)]
final class ExpressionResult
{

	/** @var (callable(bool): Type)|null */
	private $typeCallback;

	/** @var callable(MutatingScope, TypeSpecifierContext): SpecifiedTypes */
	private $specifyTypesCallback;

	/** @var (callable(MutatingScope, Type, TypeSpecifierContext): SpecifiedTypes)|null */
	private $createTypesCallback;

	private ?MutatingScope $truthyScope = null;

	private ?MutatingScope $falseyScope = null;

	private ?Type $cachedType = null;

	private ?Type $cachedNativeType = null;

	/**
	 * @param InternalThrowPoint[] $throwPoints
	 * @param ImpurePoint[] $impurePoints
	 * @param (callable(bool): Type)|null $typeCallback
	 * @param callable(MutatingScope, TypeSpecifierContext): SpecifiedTypes $specifyTypesCallback
	 * @param (callable(MutatingScope, Type, TypeSpecifierContext): SpecifiedTypes)|null $createTypesCallback
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
		?callable $typeCallback,
		callable $specifyTypesCallback,
		private bool $containsNullsafe = false,
		private ?IssetabilityDescriptor $issetabilityDescriptor = null,
		private ?MutatingScope $truthyScopeOverride = null,
		private ?MutatingScope $falseyScopeOverride = null,
		?callable $createTypesCallback = null,
		private ?Type $type = null,
		private ?Type $nativeType = null,
	)
	{
		// A precomputed type and a lazy typeCallback are mutually exclusive, but
		// exactly one of them must be set - a result with neither cannot answer its
		// own type. phpdoc and native types are precomputed together or not at all.
		if ($typeCallback !== null && $type !== null) {
			throw new ShouldNotHappenException('ExpressionResult cannot have both a typeCallback and a precomputed type.');
		}
		if ($typeCallback === null && $type === null) {
			throw new ShouldNotHappenException('ExpressionResult must have either a precomputed type or a typeCallback.');
		}
		if (($type === null) !== ($nativeType === null)) {
			throw new ShouldNotHappenException('ExpressionResult type and nativeType must both be set or both be null.');
		}

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

		// && is truthy only when the right operand was evaluated (on the left-truthy
		// scope) and is itself truthy - that is exactly $rightResult->getTruthyScope(),
		// which the handler passes as $truthyScopeOverride. It already carries the left
		// operand's narrowing and the right operand's by-ref/side-effect definitions,
		// and crucially does NOT re-apply the left narrowing on top of a scope where the
		// right operand reassigned the narrowed variable (see bug-9400).
		if ($this->truthyScopeOverride !== null) {
			return $this->truthyScope = $this->truthyScopeOverride;
		}

		return $this->truthyScope = $this->scope->applySpecifiedTypes(
			($this->specifyTypesCallback)($this->scope, TypeSpecifierContext::createTruthy()),
		);
	}

	public function getFalseyScope(): MutatingScope
	{
		if ($this->falseyScope !== null) {
			return $this->falseyScope;
		}

		// || is falsey only when the right operand was evaluated (on the left-falsey
		// scope) and is itself falsey - that is exactly $rightResult->getFalseyScope().
		if ($this->falseyScopeOverride !== null) {
			return $this->falseyScope = $this->falseyScopeOverride;
		}

		return $this->falseyScope = $this->scope->applySpecifiedTypes(
			($this->specifyTypesCallback)($this->scope, TypeSpecifierContext::createFalsey()),
		);
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

		if ($this->typeCallback !== null && !$this->hasTrackedExpressionType($this->beforeScope)) {
			return $this->cachedType = TypeUtils::resolveLateResolvableTypes(($this->typeCallback)(false));
		}

		// The guard above leaves only one way here: the expression is tracked on
		// beforeScope (typeCallback is set but a holder wins). Read the holder
		// directly instead of re-entering MutatingScope::getType().
		return $this->cachedType = $this->beforeScope->getTrackedExpressionType($this->expr);
	}

	public function getNativeType(): Type
	{
		if ($this->nativeType !== null) {
			return $this->nativeType;
		}

		if ($this->cachedNativeType !== null) {
			return $this->cachedNativeType;
		}

		if ($this->typeCallback !== null && !$this->hasTrackedExpressionType($this->beforeScope->doNotTreatPhpDocTypesAsCertain())) {
			return $this->cachedNativeType = TypeUtils::resolveLateResolvableTypes(($this->typeCallback)(true));
		}

		// Tracked native holder (getNativeType() promotes the scope, so its
		// expressionTypes are the native ones) - read it directly.
		return $this->cachedNativeType = $this->beforeScope->doNotTreatPhpDocTypesAsCertain()->getTrackedExpressionType($this->expr);
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
		return !$this->expr instanceof Expr\Variable
			&& !$this->expr instanceof Expr\Closure
			&& !$this->expr instanceof Expr\ArrowFunction
			&& $scope->hasExpressionType($this->expr)->yes();
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

	/** Evaluates this expression's narrowing on the given scope. */
	public function getSpecifiedTypesForScope(MutatingScope $scope, TypeSpecifierContext $context): SpecifiedTypes
	{
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

		if ($this->typeCallback !== null && !$this->hasTrackedExpressionType($scope)) {
			return TypeUtils::resolveLateResolvableTypes(($this->typeCallback)($scope->nativeTypesPromoted));
		}

		return $scope->getTrackedExpressionType($this->expr);
	}

	/** Native counterpart of getTypeForScope(). */
	public function getNativeTypeForScope(MutatingScope $scope): Type
	{
		if ($this->nativeType !== null) {
			return $this->nativeType;
		}

		$nativeScope = $scope->doNotTreatPhpDocTypesAsCertain();
		if ($this->typeCallback !== null && !$this->hasTrackedExpressionType($nativeScope)) {
			return TypeUtils::resolveLateResolvableTypes(($this->typeCallback)(true));
		}

		return $nativeScope->getTrackedExpressionType($this->expr);
	}

}
