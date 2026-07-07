<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

use PhpParser\Node\Expr;
use PHPStan\DependencyInjection\GenerateFactory;
use PHPStan\DependencyInjection\Type\ExpressionTypeResolverExtensionRegistryProvider;
use PHPStan\ShouldNotHappenException;
use PHPStan\Analyser\Traverser\VoidToNullTraverser;
use PHPStan\Type\Type;
use PHPStan\Type\TypeTraverser;
use PHPStan\Type\TypeUtils;
use PHPStan\Type\UnionType;
use function is_string;
use function spl_object_id;

#[GenerateFactory(interface: ExpressionResultFactory::class)]
final class ExpressionResult
{

	/** @var (callable(bool): Type)|null */
	private $typeCallback;

	/** @var callable(TypeSpecifierContext, bool): SpecifiedTypes */
	private $specifyTypesCallback;

	/** @var (callable(Type, TypeSpecifierContext, bool): SpecifiedTypes)|null */
	private $createTypesCallback;

	/** @var array<int, SpecifiedTypes> */
	private array $specifiedTypes = [];

	private ?MutatingScope $truthyScope = null;

	private ?MutatingScope $falseyScope = null;

	private ?Type $cachedType = null;

	private ?Type $cachedNativeType = null;

	private ?Type $resolvedType = null;

	private ?Type $resolvedNativeType = null;

	private ?Type $projectedType = null;

	private ?Type $projectedNativeType = null;

	/**
	 * @param InternalThrowPoint[] $throwPoints
	 * @param ImpurePoint[] $impurePoints
	 * @param (callable(bool): Type)|null $typeCallback
	 * @param callable(TypeSpecifierContext, bool): SpecifiedTypes $specifyTypesCallback
	 * @param (callable(Type, TypeSpecifierContext, bool): SpecifiedTypes)|null $createTypesCallback
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

		$type = $this->getTypeOnScope($scope, $useNativeTypes);

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
			$this->getSpecifiedTypes(TypeSpecifierContext::createTruthy(), $this->scope->nativeTypesPromoted),
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
			$this->getSpecifiedTypes(TypeSpecifierContext::createFalsey(), $this->scope->nativeTypesPromoted),
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
			return $this->cachedType = $this->resolveOwnType(false);
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
			return $this->cachedNativeType = $this->resolveOwnType(true);
		}

		// Tracked native holder (getNativeType() promotes the scope, so its
		// expressionTypes are the native ones) - read it directly.
		return $this->cachedNativeType = $this->beforeScope->doNotTreatPhpDocTypesAsCertain()->getTrackedExpressionType($this->expr);
	}

	/**
	 * The result's own raw type - the eager value or the memoized typeCallback,
	 * with no tracked-holder interference. The callback is a pure function of
	 * the flavour flag, so one memo slot per flavour is exact.
	 *
	 * A void-returning call keeps `void` here; the void->null projection every
	 * value read applies happens in resolveOwnType(). getKeepVoidType() reads
	 * this raw type so a void call used as a value (assigned, passed as an
	 * argument, a void match arm) is still seen as void by the rules that
	 * flag that misuse.
	 */
	private function resolveOwnRawType(bool $nativeTypesPromoted): Type
	{
		if ($nativeTypesPromoted) {
			if ($this->nativeType !== null) {
				return $this->nativeType;
			}
			if ($this->typeCallback === null) {
				throw new ShouldNotHappenException();
			}

			return $this->resolvedNativeType ??= TypeUtils::resolveLateResolvableTypes(($this->typeCallback)(true));
		}

		if ($this->type !== null) {
			return $this->type;
		}
		if ($this->typeCallback === null) {
			throw new ShouldNotHappenException();
		}

		return $this->resolvedType ??= TypeUtils::resolveLateResolvableTypes(($this->typeCallback)(false));
	}

	/**
	 * The result's own type as a value: the raw type with `void` projected to
	 * `null` (a void expression evaluates to null). The projection used to live
	 * in the call handlers' return-type resolution; keeping it at this single
	 * read boundary lets one raw type serve both value reads and
	 * getKeepVoidType().
	 */
	private function resolveOwnType(bool $nativeTypesPromoted): Type
	{
		if ($nativeTypesPromoted) {
			return $this->projectedNativeType ??= $this->projectVoidToNull($this->resolveOwnRawType(true));
		}

		return $this->projectedType ??= $this->projectVoidToNull($this->resolveOwnRawType(false));
	}

	private function projectVoidToNull(Type $type): Type
	{
		// void only ever originates from a call return type; the overwhelmingly
		// common non-void, non-union result skips the traverser entirely
		if ($type->isVoid()->no() && !$type instanceof UnionType) {
			return $type;
		}

		return TypeTraverser::map($type, new VoidToNullTraverser());
	}

	/**
	 * The own type with `void` kept (not projected to null) - answers
	 * Scope::getKeepVoidType() from the stored result instead of re-processing
	 * the node with a keep-void marker.
	 */
	public function getKeepVoidType(bool $nativeTypesPromoted): Type
	{
		return $this->resolveOwnRawType($nativeTypesPromoted);
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
		return $this->getSpecifiedTypes($context, $scope->nativeTypesPromoted);
	}

	/**
	 * The expression's narrowing for the given context, computed at its own
	 * evaluation point (the flavour-mapped beforeScope) and memoized per
	 * (context, flavour). All state-dependent math lives in the symbolic
	 * SpecifiedTypes (alternative terms, holder recipes, deferred augments)
	 * and is evaluated by applySpecifiedTypes() against whichever scope the
	 * narrowing is applied to - so one memoized SpecifiedTypes serves every
	 * asking position.
	 */
	public function getSpecifiedTypes(TypeSpecifierContext $context, bool $nativeTypesPromoted = false): SpecifiedTypes
	{
		$key = (spl_object_id($context) << 1) | ($nativeTypesPromoted ? 1 : 0);

		return $this->specifiedTypes[$key] ??= ($this->specifyTypesCallback)($context, $nativeTypesPromoted);
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
		return $this->getCreatedTypes($type, $context, $scope->nativeTypesPromoted);
	}

	/**
	 * The narrowing entries a type constraint on this expression fans out to,
	 * computed at the expression's own evaluation point - the asking scope
	 * reduces to its flavour bit, like getSpecifiedTypes().
	 */
	public function getCreatedTypes(Type $type, TypeSpecifierContext $context, bool $nativeTypesPromoted = false): ?SpecifiedTypes
	{
		if ($this->createTypesCallback === null) {
			return null;
		}

		return ($this->createTypesCallback)($type, $context, $nativeTypesPromoted);
	}

	/**
	 * The type of this expression as the given scope sees it: a narrowed or
	 * ensured type the scope tracks for the whole expression wins over the
	 * result's own (position-time) type. For the deliberately scope-sensitive
	 * consumers - isset/empty/?? chain folding and the stored-result read in
	 * NodeScopeResolver - everything else reads getType()/getNativeType().
	 */
	public function getTypeOnScope(MutatingScope $scope, bool $useNativeTypes, bool $repriceVariables = false): Type
	{
		$readScope = $useNativeTypes ? $scope->doNotTreatPhpDocTypesAsCertain() : $scope;
		if ($this->type === null && $this->hasTrackedExpressionType($readScope)) {
			return $readScope->getTrackedExpressionType($this->expr);
		}

		// rule-facing asks re-price a variable from the given scope: it may
		// carry narrowing this result's walk position predates (a rule asking
		// about a synthetic comparison on an arm-narrowed scope). The walk's
		// own consumers (stored-result reads, chain folds) keep the memoized
		// walk-position type - their scopes can also be WIDER (merged, loop
		// converged) than the position the value flowed from.
		if (
			$repriceVariables
			&& $this->type === null
			&& $this->expr instanceof Expr\Variable
			&& is_string($this->expr->name)
			&& !$readScope->hasVariableType($this->expr->name)->no()
		) {
			return $readScope->getVariableType($this->expr->name);
		}

		return $this->resolveOwnType($useNativeTypes);
	}

}
