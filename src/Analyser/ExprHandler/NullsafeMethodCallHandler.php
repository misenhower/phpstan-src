<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\BooleanAnd;
use PhpParser\Node\Expr\BinaryOp\NotIdentical;
use PhpParser\Node\Expr\ConstFetch;
use PhpParser\Node\Expr\MethodCall;
use PhpParser\Node\Expr\NullsafeMethodCall;
use PhpParser\Node\Name;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\ExprHandler\Helper\NonNullabilityHelper;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Node\NullsafeMethodCallExpressionNode;
use PHPStan\Node\Printer\ExprPrinter;
use PHPStan\Type\NullType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use function array_merge;

/**
 * @implements ExprHandler<NullsafeMethodCall>
 */
#[AutowiredService]
final class NullsafeMethodCallHandler implements ExprHandler
{

	public function __construct(
		private NonNullabilityHelper $nonNullabilityHelper,
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof NullsafeMethodCall;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		$scopeBeforeNullsafe = $scope;

		// the receiver's real (possibly null) type, captured before it is ensured
		// non-null below: the short-circuit decision needs to know it can be null,
		// which reading the ensured-non-null result would hide.
		$receiverType = $nodeScopeResolver->readStoredOrPriceOnDemand($expr->var, $scope);
		$receiverNativeType = $nodeScopeResolver->readStoredOrPriceOnDemandNative($expr->var, $scope);
		// carry the receiver type to NullsafeMethodCallRule so it reads it from here
		// instead of asking the scope for the unprocessed receiver.
		$nodeScopeResolver->callNodeCallbackWithExpression($nodeCallback, new NullsafeMethodCallExpressionNode($expr, $receiverType, $receiverNativeType), $beforeScope, $storage, $context);
		$nonNullabilityResult = $this->nonNullabilityHelper->ensureShallowNonNullability($nodeScopeResolver, $scope, $scope, $expr->var);
		$attributes = array_merge($expr->getAttributes(), ['virtualNullsafeMethodCall' => true]);
		unset($attributes[ExprPrinter::ATTRIBUTE_CACHE_KEY]);
		$methodCall = new MethodCall(
			$expr->var,
			$expr->name,
			$expr->args,
			$attributes,
		);
		$exprResult = $nodeScopeResolver->processExprNode(
			$stmt,
			$methodCall,
			$nonNullabilityResult->getScope(),
			$storage,
			$nodeCallback,
			$context,
		);
		$scope = $this->nonNullabilityHelper->revertNonNullability($exprResult->getScope(), $nonNullabilityResult->getSpecifiedExpressions());

		$varIsNull = $receiverType->isNull();
		if ($varIsNull->yes()) {
			// Arguments are never evaluated when the var is always null.
			$scope = $scopeBeforeNullsafe;
		} elseif ($varIsNull->maybe()) {
			// Arguments might not be evaluated (short-circuit).
			// Merge with the original scope so variables assigned in arguments become "maybe defined".
			$scope = $scope->mergeWith($scopeBeforeNullsafe);
		}

		// The `?->`'s own type on the asking scope. $receiverType is the receiver's
		// real type, captured before it was ensured non-null; reading its stored
		// result here would see the non-null device type and drop the
		// short-circuit's null.
		$nullsafeTypeCallback = static function (MutatingScope $s) use ($expr, $exprResult, $nodeScopeResolver, $receiverType): Type {
			if ($receiverType->isNull()->yes()) {
				return new NullType();
			}
			if (!TypeCombinator::containsNull($receiverType)) {
				return $exprResult->getTypeForScope($s);
			}

			// the plain method call on the null-removed scope is synthetic.
			$truthyScope = $s->filterByTruthyValue(new NotIdentical($expr->var, new ConstFetch(new Name('null'))));

			return TypeCombinator::union(
				$nodeScopeResolver->priceSyntheticOnDemand(new MethodCall($expr->var, $expr->name, $expr->args), $truthyScope),
				new NullType(),
			);
		};

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $exprResult->hasYield(),
			isAlwaysTerminating: false,
			throwPoints: $exprResult->getThrowPoints(),
			impurePoints: $exprResult->getImpurePoints(),
			containsNullsafe: true,
			typeCallback: $nullsafeTypeCallback,
			specifyTypesCallback: function (MutatingScope $s, TypeSpecifierContext $context) use ($expr, $methodCall, $nodeScopeResolver): SpecifiedTypes {
				if ($context->null()) {
					return $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
				}

				$types = $this->defaultNarrowingHelper->specifyTypesForNode(
					$s,
					new BooleanAnd(
						new NotIdentical($expr->var, new ConstFetch(new Name('null'))),
						$methodCall,
					),
					$context,
				)->setRootExpr($expr);

				$nullSafeTypes = $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);
				return $context->true() ? $types->unionWith($nullSafeTypes) : $types->normalize($s, $nodeScopeResolver)->intersectWith($nullSafeTypes->normalize($s, $nodeScopeResolver));
			},
			// Inside-out copy of TypeSpecifier::createForExpr()'s `?->` handling.
			// The short-circuit's null surfaces here, never by walking the chain:
			// a receiver that is itself a ?-> composes through the parent handler.
			createTypesCallback: function (MutatingScope $s, Type $type, TypeSpecifierContext $context) use ($expr, $methodCall, $exprResult, $nullsafeTypeCallback): SpecifiedTypes {
				// null() context: createForExpr never computes $containsNull and
				// emits no entry for the subject - behave the same.
				if ($context->null()) {
					return (new SpecifiedTypes())->setRootExpr($expr);
				}

				$nullsafeType = $nullsafeTypeCallback($s);
				if ($context->true()) {
					$containsNull = !$type->isNull()->no() && !$nullsafeType->isNull()->no();
				} else {
					$containsNull = !TypeCombinator::containsNull($type) && !$nullsafeType->isNull()->no();
				}

				// The ?-> may legitimately be null (e.g. narrowed to a nullable
				// $type): keep the ?-> node's own key only, no plain chain, no
				// receiver-not-null - exactly createForExpr's containsNull branch.
				if ($containsNull) {
					return $this->defaultNarrowingHelper->createSubjectTypes($s, $expr, null, $type, $context)->setRootExpr($expr);
				}

				// !containsNull: the plain inner methodCall narrowed by $type
				// (createNullsafeTypes), the original ?-> key (createForExpr's
				// double-key), and "receiver is not null".
				return $this->defaultNarrowingHelper->createSubjectTypes($s, $methodCall, $exprResult, $type, $context)
					->unionWith($this->defaultNarrowingHelper->createSubjectTypes($s, $expr, null, $type, $context))
					->unionWith($this->defaultNarrowingHelper->createSubjectTypes($s, $expr->var, null, new NullType(), TypeSpecifierContext::createFalse()))
					->setRootExpr($expr);
			},
		);
	}

}
