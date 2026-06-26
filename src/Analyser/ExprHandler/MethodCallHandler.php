<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\Identical;
use PhpParser\Node\Expr\MethodCall;
use PhpParser\Node\Identifier;
use PhpParser\Node\Scalar\String_;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ArgumentsNormalizer;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\ExprHandler\Helper\MethodCallReturnTypeHelper;
use PHPStan\Analyser\ExprHandler\Helper\MethodThrowPointHelper;
use PHPStan\Analyser\ImpurePoint;
use PHPStan\Analyser\InternalThrowPoint;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\NoopNodeCallback;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifier;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredParameter;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\Expr\PossiblyImpureCallExpr;
use PHPStan\Node\InvalidateExprNode;
use PHPStan\Reflection\Callables\SimpleImpurePoint;
use PHPStan\Reflection\ExtendedParametersAcceptor;
use PHPStan\Reflection\ParametersAcceptor;
use PHPStan\Reflection\ParametersAcceptorSelector;
use PHPStan\Reflection\ReflectionProvider;
use PHPStan\Type\ErrorType;
use PHPStan\Type\Generic\TemplateTypeHelper;
use PHPStan\Type\Generic\TemplateTypeVariance;
use PHPStan\Type\Generic\TemplateTypeVarianceMap;
use PHPStan\Type\MixedType;
use PHPStan\Type\NeverType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use PHPStan\Type\TypeUtils;
use function array_map;
use function array_merge;
use function count;
use function sprintf;
use function strtolower;

/**
 * @implements ExprHandler<MethodCall>
 */
#[AutowiredService]
final class MethodCallHandler implements ExprHandler
{

	public function __construct(
		private MethodCallReturnTypeHelper $methodCallReturnTypeHelper,
		private MethodThrowPointHelper $methodThrowPointHelper,
		private ReflectionProvider $reflectionProvider,
		#[AutowiredParameter]
		private bool $rememberPossiblyImpureFunctionValues,
		private ExpressionResultFactory $expressionResultFactory,
		private TypeSpecifier $typeSpecifier,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof MethodCall && !$expr->isFirstClassCallable();
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		$originalScope = $scope;
		if (
			($expr->var instanceof Expr\Closure || $expr->var instanceof Expr\ArrowFunction)
			&& $expr->name instanceof Identifier
			&& strtolower($expr->name->name) === 'call'
			&& isset($expr->getArgs()[0])
		) {
			// process the new-$this argument as a read so enterClosureCall() consumes
			// its stored ExpressionResult instead of reading the unprocessed node via
			// Scope::getType(). processArgs() below processes it again as call()'s first
			// argument; the NoopNodeCallback here avoids a duplicate node-callback.
			$newThisResult = $nodeScopeResolver->processExprNode($stmt, $expr->getArgs()[0]->value, $scope, $storage, new NoopNodeCallback(), $context->enterDeep());
			$closureCallScope = $scope->enterClosureCall(
				$newThisResult->getTypeForScope($scope),
				$newThisResult->getNativeTypeForScope($scope),
			);
		}

		$varResult = $nodeScopeResolver->processExprNode($stmt, $expr->var, $closureCallScope ?? $scope, $storage, $nodeCallback, $context->enterDeep());
		$hasYield = $varResult->hasYield();
		$throwPoints = $varResult->getThrowPoints();
		$impurePoints = $varResult->getImpurePoints();
		$isAlwaysTerminating = $varResult->isAlwaysTerminating();
		$scope = $varResult->getScope();
		if (isset($closureCallScope)) {
			$scope = $scope->restoreOriginalScopeAfterClosureBind($originalScope);
		}
		$parametersAcceptor = null;
		$variants = [];
		$namedArgumentsVariants = null;
		$methodReflection = null;
		$nameResult = null;
		// the var was processed above as the receiver; read its already-computed
		// result instead of re-walking via Scope::getType().
		$calledOnType = $varResult->getTypeForScope($scope);
		if ($expr->name instanceof Identifier) {
			$methodName = $expr->name->name;
			$methodReflection = $scope->getMethodReflection($calledOnType, $methodName);
			if ($methodReflection !== null) {
				$variants = $methodReflection->getVariants();
				$namedArgumentsVariants = $methodReflection->getNamedArgumentsVariants();
				// A structural acceptor (names/positions/variadic) drives argument
				// normalization, the impure point and the throw point - generics are
				// resolved type-driven by processArgs() into $resolvedParametersAcceptor.
				$parametersAcceptor = ParametersAcceptorSelector::combineVariantsForNormalization($expr->getArgs(), $variants, $namedArgumentsVariants);
			}
		} else {
			$nameResult = $nodeScopeResolver->processExprNode($stmt, $expr->name, $scope, $storage, $nodeCallback, $context->enterDeep());
			$throwPoints = array_merge($throwPoints, $nameResult->getThrowPoints());
			$scope = $nameResult->getScope();
		}

		if ($methodReflection !== null) {
			$impurePoint = SimpleImpurePoint::createFromVariant($methodReflection, $parametersAcceptor, $scope, $expr->getArgs());
			if ($impurePoint !== null) {
				$impurePoints[] = new ImpurePoint($scope, $expr, $impurePoint->getIdentifier(), $impurePoint->getDescription(), $impurePoint->isCertain());
			}
		} else {
			$impurePoints[] = new ImpurePoint(
				$scope,
				$expr,
				'methodCall',
				'call to unknown method',
				false,
			);
		}

		$normalizedExpr = $expr;
		if ($parametersAcceptor !== null) {
			$normalizedExpr = ArgumentsNormalizer::reorderMethodArguments($parametersAcceptor, $expr) ?? $expr;
			$returnType = $parametersAcceptor->getReturnType();
			$isAlwaysTerminating = $isAlwaysTerminating || ($returnType instanceof NeverType && $returnType->isExplicit());
		}

		$argsResult = $nodeScopeResolver->processArgs(
			$stmt,
			$methodReflection,
			$methodReflection !== null ? $scope->getNakedMethod($calledOnType, $methodReflection->getName()) : null,
			$variants,
			$namedArgumentsVariants,
			$normalizedExpr,
			$scope,
			$storage,
			$nodeCallback,
			$context,
		);
		$resolvedParametersAcceptor = $argsResult->getResolvedParametersAcceptor();
		$scope = $argsResult->getScope();
		$nodeScopeResolver->processDroppedArgs($stmt, $expr, $normalizedExpr, $scope, $storage, $context);

		// The return type is derived from $resolvedParametersAcceptor - the acceptor
		// processArgs() selected from the arg types gathered on the arg-to-arg
		// evolving scope (type-driven, generics resolved). When null
		// (native-types-promoted, or on-demand / synthetic pricing) the acceptor is
		// re-derived from the already-processed argument results on the asking scope.
		$typeCallback = fn (MutatingScope $s): Type => $this->resolveReturnType(
			$nodeScopeResolver,
			$s,
			$expr,
			$varResult,
			$nameResult,
			$s->nativeTypesPromoted ? null : $resolvedParametersAcceptor,
		);
		$specifyTypesCallback = fn (MutatingScope $s, TypeSpecifierContext $specifyContext): SpecifiedTypes => $this->specifyTypes(
			$nodeScopeResolver,
			$s,
			$expr,
			$normalizedExpr,
			$varResult,
			$resolvedParametersAcceptor,
			$specifyContext,
		);

		// A type constraint on a (narrowable, i.e. non-side-effecting) method call
		// narrows the call itself - the inside-out equivalent of createForExpr's
		// MethodCall purity gate + tail entry. An impure call narrows to nothing.
		$createTypesCallback = fn (MutatingScope $s, Type $type, TypeSpecifierContext $createContext): SpecifiedTypes => $this->isMethodCallNarrowable($s, $expr, $varResult)
			? $this->defaultNarrowingHelper->createSubjectTypes($s, $expr, null, $type, $createContext)
			: new SpecifiedTypes([], []);

		// Store a preliminary result carrying the type/specify callbacks before the
		// throw point is computed: the method throw point resolves the return type
		// (resolveReturnType below) through dynamic return type extensions, which can
		// narrow this very call on demand. Without a stored result that narrowing
		// would re-process this MethodCall on demand and recurse. The callbacks are
		// scope-independent, so the preliminary result answers those asks correctly;
		// the final result below overwrites it with the resolved scope and
		// throw/impure points.
		$nodeScopeResolver->storeExpressionResult($storage, $expr, $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $hasYield,
			isAlwaysTerminating: $isAlwaysTerminating,
			throwPoints: [],
			impurePoints: [],
			containsNullsafe: $varResult->containsNullsafe(),
			typeCallback: $typeCallback,
			specifyTypesCallback: $specifyTypesCallback,
			createTypesCallback: $createTypesCallback,
		));

		if ($methodReflection !== null) {
			// The early structural check above only sees the unresolved acceptor
			// return type; a conditional-return never (e.g. `($x is Foo ? never :
			// string)`) only resolves to never once the actual argument types are
			// folded in by the type-driven resolved acceptor.
			if ($resolvedParametersAcceptor !== null) {
				$resolvedReturnType = $resolvedParametersAcceptor->getReturnType();
				$isAlwaysTerminating = $isAlwaysTerminating || ($resolvedReturnType instanceof NeverType && $resolvedReturnType->isExplicit());
			}

			// The call's return type, computed from the already-processed argument
			// results (resolveReturnType reads them via the receiver/name results and
			// readStoredOrPriceOnDemand, never re-running processArgs) - asking
			// Scope::getType() for the MethodCall here would re-enter this handler on
			// demand, as its final result is not stored yet.
			$methodCallReturnType = $this->resolveReturnType($nodeScopeResolver, $scope, $expr, $varResult, $nameResult, $resolvedParametersAcceptor);
			$methodThrowPoint = $this->methodThrowPointHelper->getThrowPoint($methodReflection, $parametersAcceptor, $normalizedExpr, $scope, $context, $methodCallReturnType);
			if ($methodThrowPoint !== null) {
				$throwPoints[] = $methodThrowPoint;
			}

			if ($methodReflection->getName() === '__construct' || $methodReflection->hasSideEffects()->yes()) {
				$nodeScopeResolver->callNodeCallback($nodeCallback, new InvalidateExprNode($normalizedExpr->var), $scope, $storage);
				$scope = $scope->invalidateExpression($normalizedExpr->var, true, $methodReflection->getDeclaringClass());
			} elseif ($this->rememberPossiblyImpureFunctionValues && $methodReflection->hasSideEffects()->maybe() && !$methodReflection->getDeclaringClass()->isBuiltin()) {
				// the remembered call value and the @phpstan-self-out type are
				// generic-sensitive: resolve them from the type-driven acceptor
				// processArgs() selected (generics resolved against the actual arg
				// types), falling back to the structural acceptor for dynamic callees.
				$acceptorForGenerics = $resolvedParametersAcceptor ?? $parametersAcceptor;
				$scope = $scope->assignExpression(
					new PossiblyImpureCallExpr($normalizedExpr, $normalizedExpr->var, sprintf('%s::%s()', $methodReflection->getDeclaringClass()->getDisplayName(), $methodReflection->getName())),
					$acceptorForGenerics->getReturnType(),
					new MixedType(),
				);
			}
			if (!$methodReflection->isStatic()) {
				$selfOutType = $methodReflection->getSelfOutType();
				if ($selfOutType !== null) {
					$acceptorForGenerics = $resolvedParametersAcceptor ?? $parametersAcceptor;
					$scope = $scope->assignExpression(
						$normalizedExpr->var,
						TemplateTypeHelper::resolveTemplateTypes(
							$selfOutType,
							$acceptorForGenerics->getResolvedTemplateTypeMap(),
							$acceptorForGenerics instanceof ExtendedParametersAcceptor ? $acceptorForGenerics->getCallSiteVarianceMap() : TemplateTypeVarianceMap::createEmpty(),
							TemplateTypeVariance::createCovariant(),
						),
						$varResult->getNativeTypeForScope($scope),
					);
				}
			}

		} else {
			$nodeScopeResolver->callNodeCallback($nodeCallback, new InvalidateExprNode($normalizedExpr->var), $scope, $storage);
			$scope = $scope->invalidateExpression($normalizedExpr->var, true);
			$throwPoints[] = InternalThrowPoint::createImplicit($scope, $expr);
		}
		if (
			$methodReflection === null
			|| (!$methodReflection->getDeclaringClass()->isBuiltin() && !$methodReflection->hasSideEffects()->no())
		) {
			$scope = $scope->invalidateVolatileExpressions();
		}

		$hasYield = $hasYield || $argsResult->hasYield();
		$throwPoints = array_merge($throwPoints, $argsResult->getThrowPoints());
		$impurePoints = array_merge($impurePoints, $argsResult->getImpurePoints());
		$isAlwaysTerminating = $isAlwaysTerminating || $argsResult->isAlwaysTerminating();

		$result = $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $hasYield,
			isAlwaysTerminating: $isAlwaysTerminating,
			throwPoints: $throwPoints,
			impurePoints: $impurePoints,
			containsNullsafe: $varResult->containsNullsafe(),
			typeCallback: $typeCallback,
			specifyTypesCallback: $specifyTypesCallback,
			createTypesCallback: $createTypesCallback,
		);

		// the var was processed above as the receiver; read its already-computed
		// result on the original scope instead of re-walking via Scope::getType().
		$calledOnType = $varResult->getTypeForScope($originalScope);
		if (!$expr->name instanceof Identifier) {
			return $result;
		}
		$methodName = $expr->name->name;
		$methodReflection = $originalScope->getMethodReflection($calledOnType, $methodName);
		if ($methodReflection === null) {
			return $result;
		}
		if (
			$scope->isInClass()
			&& $scope->getClassReflection()->getName() === $methodReflection->getDeclaringClass()->getName()
			&& ($scope->getFunctionName() !== null && strtolower($scope->getFunctionName()) === '__construct')
			&& TypeUtils::findThisType($calledOnType) !== null
		) {
			$calledMethodScope = $nodeScopeResolver->processCalledMethod($methodReflection);
			if ($calledMethodScope !== null) {
				$scope = $scope->mergeInitializedProperties($calledMethodScope);
				return $this->expressionResultFactory->create(
					$scope,
					beforeScope: $beforeScope,
					expr: $expr,
					hasYield: $result->hasYield(),
					isAlwaysTerminating: $result->isAlwaysTerminating(),
					throwPoints: $result->getThrowPoints(),
					impurePoints: $result->getImpurePoints(),
					containsNullsafe: $varResult->containsNullsafe(),
					typeCallback: $typeCallback,
					specifyTypesCallback: $specifyTypesCallback,
					createTypesCallback: $createTypesCallback,
				);
			}
		}

		return $result;
	}

	/**
	 * The call-expression type is derived from $preResolvedAcceptor - the acceptor
	 * processArgs() selected from the arg types gathered on the arg-to-arg evolving
	 * scope (type-driven, generics resolved). When null (native-types-promoted, or
	 * on-demand / synthetic pricing) it falls back to re-selecting from the args via
	 * MethodCallReturnTypeHelper on the asking scope.
	 *
	 * The receiver/name were processed during processExpr; their already computed
	 * results are read instead of re-walking via Scope::getType(). The dynamic-name
	 * branch builds a synthetic MethodCall priced on demand by the resolver.
	 *
	 * @param MethodCall $expr
	 */
	private function resolveReturnType(NodeScopeResolver $nodeScopeResolver, MutatingScope $scope, Expr $expr, ExpressionResult $varResult, ?ExpressionResult $nameResult, ?ParametersAcceptor $preResolvedAcceptor): Type
	{
		// a call on a nullsafe chain whose receiver is currently nullable
		// short-circuits to null - the receiver result carries whether the chain
		// contains a ?-> (a plain nullable receiver does not propagate).
		$shortCircuit = static fn (Type $type): Type => $varResult->containsNullsafe() && TypeCombinator::containsNull($varResult->getTypeForScope($scope))
			? TypeCombinator::addNull($type)
			: $type;

		if ($expr->name instanceof Identifier) {
			if ($scope->nativeTypesPromoted) {
				$methodReflection = $scope->getMethodReflection(
					$varResult->getNativeTypeForScope($scope),
					$expr->name->name,
				);
				if ($methodReflection === null) {
					$returnType = new ErrorType();
				} else {
					$returnType = ParametersAcceptorSelector::combineAcceptors($methodReflection->getVariants())->getNativeReturnType();
				}

				return $shortCircuit($returnType);
			}

			$returnType = $this->methodCallReturnTypeHelper->methodCallReturnType(
				$scope,
				$varResult->getTypeForScope($scope),
				$expr->name->name,
				$expr,
				$preResolvedAcceptor,
			);
			if ($returnType === null) {
				$returnType = new ErrorType();
			}
			return $shortCircuit($returnType);
		}

		$nameType = $nameResult !== null ? $nameResult->getTypeForScope($scope) : $nodeScopeResolver->readStoredOrPriceOnDemand($expr->name, $scope);
		if (count($nameType->getConstantStrings()) > 0) {
			return TypeCombinator::union(
				...array_map(static function ($constantString) use ($expr, $scope, $nodeScopeResolver): Type {
					if ($constantString->getValue() === '') {
						return new ErrorType();
					}

					// a method call with a concrete name on the name-pinned scope
					// is synthetic.
					$truthyScope = $scope->applySpecifiedTypes($nodeScopeResolver->processExprOnDemand(new Identical($expr->name, new String_($constantString->getValue())), $scope, new ExpressionResultStorage())->getSpecifiedTypesForScope($scope, TypeSpecifierContext::createTruthy()));

					return $nodeScopeResolver->priceSyntheticOnDemand(
						new MethodCall($expr->var, new Identifier($constantString->getValue()), $expr->args),
						$truthyScope,
					);
				}, $nameType->getConstantStrings()),
			);
		}

		return new MixedType();
	}

	/**
	 * Ported inside-out from the old TypeResolvingExprHandler::specifyTypes(): the
	 * MethodTypeSpecifyingExtensions, conditional-return-type and @phpstan-assert
	 * narrowing are invoked on the already-processed argument results. The acceptor
	 * is $resolvedParametersAcceptor (type-driven, generics resolved by processArgs)
	 * rather than re-selected from the args on the asking scope. The subject's own
	 * default narrowing comes from DefaultNarrowingHelper instead of
	 * TypeSpecifier::handleDefaultTruthyOrFalseyContext(), which would re-enter this
	 * expression through TypeSpecifier::create().
	 *
	 * @param MethodCall $expr
	 * @param MethodCall $normalizedExpr
	 */
	private function specifyTypes(NodeScopeResolver $nodeScopeResolver, MutatingScope $scope, Expr $expr, Expr $normalizedExpr, ExpressionResult $varResult, ?ParametersAcceptor $resolvedParametersAcceptor, TypeSpecifierContext $context): SpecifiedTypes
	{
		if (!$expr->name instanceof Identifier) {
			return $this->defaultMethodCallNarrowing($scope, $expr, $varResult, $context);
		}

		// the var was processed during processExpr; read its already-computed
		// result instead of re-walking via Scope::getType().
		$methodCalledOnType = $varResult->getTypeForScope($scope);
		$methodReflection = $scope->getMethodReflection($methodCalledOnType, $expr->name->name);
		if ($methodReflection !== null) {
			$args = $expr->getArgs();

			$referencedClasses = $methodCalledOnType->getObjectClassNames();
			if (
				count($referencedClasses) === 1
				&& $this->reflectionProvider->hasClass($referencedClasses[0])
			) {
				$methodClassReflection = $this->reflectionProvider->getClass($referencedClasses[0]);
				foreach ($this->typeSpecifier->getMethodTypeSpecifyingExtensionsForClass($methodClassReflection->getName()) as $extension) {
					if (!$extension->isMethodSupported($methodReflection, $normalizedExpr, $context)) {
						continue;
					}

					return $extension->specifyTypes($methodReflection, $normalizedExpr, $scope, $context);
				}
			}

			if (count($args) > 0 && $resolvedParametersAcceptor !== null) {
				$specifiedTypes = $this->typeSpecifier->specifyTypesFromConditionalReturnType($context, $expr, $resolvedParametersAcceptor, $scope);
				if ($specifiedTypes !== null) {
					return $specifiedTypes;
				}
			}

			$assertions = $methodReflection->getAsserts();
			if ($assertions->getAll() !== [] && $resolvedParametersAcceptor !== null) {
				$asserts = $assertions->mapTypes(static fn (Type $type) => TemplateTypeHelper::resolveTemplateTypes(
					$type,
					$resolvedParametersAcceptor->getResolvedTemplateTypeMap(),
					$resolvedParametersAcceptor instanceof ExtendedParametersAcceptor ? $resolvedParametersAcceptor->getCallSiteVarianceMap() : TemplateTypeVarianceMap::createEmpty(),
					TemplateTypeVariance::createInvariant(),
				));
				$specifiedTypes = $this->typeSpecifier->specifyTypesFromAsserts($context, $expr, $asserts, $resolvedParametersAcceptor, $scope);
				if ($specifiedTypes !== null) {
					return $specifiedTypes
						->unionWith($this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context))
						->setRootExpr($specifiedTypes->getRootExpr());
				}
			}
		}

		return $this->defaultMethodCallNarrowing($scope, $expr, $varResult, $context);
	}

	/**
	 * The default truthy/falsey narrowing of the call expression itself, gated by
	 * the same purity check TypeSpecifier::create() applies: a method with side
	 * effects (or an unknown method whose result is not remembered) is not
	 * narrowable - calling it twice may yield different values - so it contributes
	 * no entry. Mirrors create()'s MethodCall handling inside-out, without
	 * re-entering this expression through create().
	 *
	 * @param MethodCall $expr
	 */
	private function defaultMethodCallNarrowing(MutatingScope $scope, Expr $expr, ExpressionResult $varResult, TypeSpecifierContext $context): SpecifiedTypes
	{
		if (!$this->isMethodCallNarrowable($scope, $expr, $varResult)) {
			return (new SpecifiedTypes([], []))->setRootExpr($expr);
		}

		return $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
	}

	/** @param MethodCall $expr */
	private function isMethodCallNarrowable(MutatingScope $scope, Expr $expr, ExpressionResult $varResult): bool
	{
		if (!$expr->name instanceof Identifier) {
			return true;
		}

		$calledOnType = $varResult->getTypeForScope($scope);
		$methodReflection = $scope->getMethodReflection($calledOnType, $expr->name->toString());
		if ($methodReflection === null) {
			return false;
		}

		$hasSideEffects = $methodReflection->hasSideEffects();
		if ($hasSideEffects->yes()) {
			return false;
		}

		return $this->rememberPossiblyImpureFunctionValues || $hasSideEffects->no();
	}

}
