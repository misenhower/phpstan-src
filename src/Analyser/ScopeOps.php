<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

use PhpParser\Node;
use PhpParser\Node\Expr;
use PhpParser\Node\Expr\FuncCall;
use PhpParser\Node\Expr\MethodCall;
use PhpParser\Node\Expr\Variable;
use PhpParser\NodeFinder;
use PHPStan\Node\Printer\ExprPrinter;
use PHPStan\Node\VirtualNode;
use PHPStan\Parser\ArrayMapArgVisitor;
use PHPStan\Reflection\FunctionReflection;
use PHPStan\Reflection\MethodReflection;
use PHPStan\Reflection\ParameterReflection;
use PHPStan\TrinaryLogic;
use PHPStan\Type\ErrorType;
use PHPStan\Type\Type;
use function array_filter;
use function array_key_exists;
use function array_keys;
use function count;
use function in_array;
use function is_string;

/**
 * Hot scope-table operations extracted from MutatingScope.
 *
 * When the phpstan_turbo extension is loaded, this class is shadowed by a stub
 * extending the extension's native implementation (see
 * PHPStan\Turbo\TurboExtensionEnabler), so every method here must behave
 * exactly like its native counterpart.
 */
final class ScopeOps
{

	private const CONTAINS_SUPER_GLOBAL_ATTRIBUTE_NAME = 'containsSuperGlobal';

	/**
	 * Mirrors MutatingScope::getNodeKey().
	 */
	public static function nodeKey(Expr $node, ExprPrinter $exprPrinter): string
	{
		// perf optimize for the most common path
		if ($node instanceof Variable && !$node->name instanceof Expr) {
			return '$' . $node->name;
		}

		$key = $exprPrinter->printExpr($node);
		$attributes = $node->getAttributes();
		if (
			$node instanceof Node\FunctionLike
			&& (($attributes[ArrayMapArgVisitor::ATTRIBUTE_NAME] ?? null) !== null)
			&& (($attributes['startFilePos'] ?? null) !== null)
		) {
			$key .= '/*' . $attributes['startFilePos'];
			foreach ($attributes[ArrayMapArgVisitor::ATTRIBUTE_NAME] as $arg) {
				$key .= ':' . $exprPrinter->printExpr($arg->value);
			}
			$key .= '*/';
		}

		return $key;
	}

	/**
	 * The memo-hit fast path of MutatingScope::getType(). Returns the resolved
	 * type on a cache hit; on a miss returns null and assigns the computed
	 * node key to $key so the caller can continue without recomputing it.
	 *
	 * @param-out string $key
	 */
	public static function getTypeFromCache(MutatingScope $scope, Expr $node, ?string &$key): ?Type
	{
		$key = self::nodeKey($node, $scope->getExprPrinter());

		return $scope->resolvedTypes[$key] ?? null;
	}

	/**
	 * The tracked-expression fast path of MutatingScope::resolveType(): for
	 * non-Variable/Closure/ArrowFunction nodes whose expressionTypes entry has
	 * certainty Yes, returns the tracked type; null otherwise.
	 */
	public static function expressionTypeByKey(MutatingScope $scope, Expr $node, string $exprString): ?Type
	{
		if (
			$node instanceof Variable
			|| $node instanceof Expr\Closure
			|| $node instanceof Expr\ArrowFunction
		) {
			return null;
		}

		$holder = $scope->expressionTypes[$exprString] ?? null;
		if ($holder === null || !$holder->getCertainty()->yes()) {
			return null;
		}

		return $holder->getType();
	}

	/**
	 * Mirrors MutatingScope::hasExpressionType().
	 */
	public static function hasExpressionType(MutatingScope $scope, Expr $node, ExprPrinter $exprPrinter): TrinaryLogic
	{
		if ($node instanceof Variable && is_string($node->name)) {
			return self::hasVariableType($scope, $node->name);
		}

		$exprString = self::nodeKey($node, $exprPrinter);
		if (!isset($scope->expressionTypes[$exprString])) {
			return TrinaryLogic::createNo();
		}
		return $scope->expressionTypes[$exprString]->getCertainty();
	}

	/**
	 * Mirrors MutatingScope::hasVariableType().
	 */
	public static function hasVariableType(MutatingScope $scope, string $variableName): TrinaryLogic
	{
		if (in_array($variableName, Scope::SUPERGLOBAL_VARIABLES, true)) {
			return TrinaryLogic::createYes();
		}

		$varExprString = '$' . $variableName;
		if (!isset($scope->expressionTypes[$varExprString])) {
			if ($scope->canAnyVariableExist()) {
				return TrinaryLogic::createMaybe();
			}

			return TrinaryLogic::createNo();
		}

		return $scope->expressionTypes[$varExprString]->getCertainty();
	}

	/**
	 * Clone-like scope creation with unchanged context; only the expression
	 * tables and a couple of flags differ from the given scope.
	 *
	 * @param array<string, ExpressionTypeHolder> $expressionTypes
	 * @param array<string, ExpressionTypeHolder> $nativeExpressionTypes
	 * @param array<string, ConditionalExpressionHolder[]> $conditionalExpressions
	 * @param array<string, bool> $currentlyAssignedExpressions
	 * @param array<string, true> $currentlyAllowedUndefinedExpressions
	 * @param list<array{FunctionReflection|MethodReflection|null, ParameterReflection|null}> $inFunctionCallsStack
	 */
	public static function scopeWith(
		MutatingScope $scope,
		array $expressionTypes,
		array $nativeExpressionTypes,
		array $conditionalExpressions,
		array $currentlyAssignedExpressions,
		array $currentlyAllowedUndefinedExpressions,
		array $inFunctionCallsStack,
		bool $inFirstLevelStatement,
		bool $afterExtractCall,
	): MutatingScope
	{
		return $scope->duplicateWith(
			$expressionTypes,
			$nativeExpressionTypes,
			$conditionalExpressions,
			$currentlyAssignedExpressions,
			$currentlyAllowedUndefinedExpressions,
			$inFunctionCallsStack,
			$inFirstLevelStatement,
			$afterExtractCall,
		);
	}

	/**
	 * Mirrors the former MutatingScope::mergeVariableHolders().
	 *
	 * @param array<string, ExpressionTypeHolder> $ourVariableTypeHolders
	 * @param array<string, ExpressionTypeHolder> $theirVariableTypeHolders
	 * @param array<string, true> $differingKeys
	 * @return array<string, ExpressionTypeHolder>
	 */
	public static function mergeVariableHolders(array $ourVariableTypeHolders, array $theirVariableTypeHolders, array &$differingKeys = []): array
	{
		$intersectedVariableTypeHolders = [];
		$globalVariableCallback = static fn (Node $node) => $node instanceof Variable && is_string($node->name) && in_array($node->name, Scope::SUPERGLOBAL_VARIABLES, true);
		$nodeFinder = new NodeFinder();
		foreach ($ourVariableTypeHolders as $exprString => $variableTypeHolder) {
			if (isset($theirVariableTypeHolders[$exprString])) {
				if ($variableTypeHolder === $theirVariableTypeHolders[$exprString]) {
					$intersectedVariableTypeHolders[$exprString] = $variableTypeHolder;
					continue;
				}

				$differingKeys[$exprString] = true;
				$intersectedVariableTypeHolders[$exprString] = $variableTypeHolder->and($theirVariableTypeHolders[$exprString]);
			} else {
				$differingKeys[$exprString] = true;
				$expr = $variableTypeHolder->getExpr();

				$containsSuperGlobal = $expr->getAttribute(self::CONTAINS_SUPER_GLOBAL_ATTRIBUTE_NAME);
				if ($containsSuperGlobal === null) {
					$containsSuperGlobal = $nodeFinder->findFirst($expr, $globalVariableCallback) !== null;
					$expr->setAttribute(self::CONTAINS_SUPER_GLOBAL_ATTRIBUTE_NAME, $containsSuperGlobal);
				}
				if ($containsSuperGlobal === true) {
					continue;
				}

				$intersectedVariableTypeHolders[$exprString] = ExpressionTypeHolder::createMaybe($expr, $variableTypeHolder->getType());
			}
		}

		foreach ($theirVariableTypeHolders as $exprString => $variableTypeHolder) {
			if (isset($intersectedVariableTypeHolders[$exprString])) {
				continue;
			}

			$differingKeys[$exprString] = true;
			$expr = $variableTypeHolder->getExpr();

			$containsSuperGlobal = $expr->getAttribute(self::CONTAINS_SUPER_GLOBAL_ATTRIBUTE_NAME);
			if ($containsSuperGlobal === null) {
				$containsSuperGlobal = $nodeFinder->findFirst($expr, $globalVariableCallback) !== null;
				$expr->setAttribute(self::CONTAINS_SUPER_GLOBAL_ATTRIBUTE_NAME, $containsSuperGlobal);
			}
			if ($containsSuperGlobal === true) {
				continue;
			}

			$intersectedVariableTypeHolders[$exprString] = ExpressionTypeHolder::createMaybe($expr, $variableTypeHolder->getType());
		}

		return $intersectedVariableTypeHolders;
	}

	/**
	 * The tail of MutatingScope::mergeWith() after conditional expressions were
	 * handled: filters the merged expression types and computes the merged
	 * native expression types.
	 *
	 * @param array<string, ExpressionTypeHolder> $mergedExpressionTypes
	 * @param array<string, ExpressionTypeHolder> $ourExpressionTypes
	 * @param array<string, ExpressionTypeHolder> $theirExpressionTypes
	 * @param array<string, ExpressionTypeHolder> $ourNativeExpressionTypes
	 * @param array<string, ExpressionTypeHolder> $theirNativeExpressionTypes
	 * @return array{array<string, ExpressionTypeHolder>, array<string, ExpressionTypeHolder>}
	 */
	public static function finishMerge(
		array $mergedExpressionTypes,
		array $ourExpressionTypes,
		array $theirExpressionTypes,
		array $ourNativeExpressionTypes,
		array $theirNativeExpressionTypes,
	): array
	{
		$filter = static function (ExpressionTypeHolder $expressionTypeHolder) {
			if ($expressionTypeHolder->getCertainty()->yes()) {
				return true;
			}

			$expr = $expressionTypeHolder->getExpr();

			return $expr instanceof Variable
				|| $expr instanceof FuncCall
				|| $expr instanceof VirtualNode;
		};

		$mergedExpressionTypes = array_filter($mergedExpressionTypes, $filter);

		$mergedNativeExpressionTypes = [];
		foreach ($ourNativeExpressionTypes as $exprString => $expressionTypeHolder) {
			if (!array_key_exists($exprString, $theirNativeExpressionTypes)) {
				continue;
			}
			if (!array_key_exists($exprString, $ourExpressionTypes)) {
				continue;
			}
			if (!array_key_exists($exprString, $theirExpressionTypes)) {
				continue;
			}
			if (!$expressionTypeHolder->equals($ourExpressionTypes[$exprString])) {
				continue;
			}
			if (!$theirNativeExpressionTypes[$exprString]->equals($theirExpressionTypes[$exprString])) {
				continue;
			}
			if (!array_key_exists($exprString, $mergedExpressionTypes)) {
				continue;
			}
			$mergedNativeExpressionTypes[$exprString] = $mergedExpressionTypes[$exprString];
			unset($ourNativeExpressionTypes[$exprString]);
			unset($theirNativeExpressionTypes[$exprString]);
		}

		return [
			$mergedExpressionTypes,
			// + instead of array_merge: the key sets are disjoint (matching entries were
			// unset from both native maps above), and array_merge would renumber
			// integer-coerced expression keys (an expression printing as '5' is stored
			// under int key 5), corrupting them. The native implementation preserves keys.
			$mergedNativeExpressionTypes + array_filter(self::mergeVariableHolders($ourNativeExpressionTypes, $theirNativeExpressionTypes), $filter),
		];
	}

	/**
	 * Mirrors the former MutatingScope::intersectConditionalExpressions().
	 *
	 * @param array<string, ConditionalExpressionHolder[]> $ourConditionalExpressions
	 * @param array<string, ConditionalExpressionHolder[]> $theirConditionalExpressions
	 * @return array<string, ConditionalExpressionHolder[]>
	 */
	public static function intersectConditionalExpressions(array $ourConditionalExpressions, array $theirConditionalExpressions): array
	{
		$newConditionalExpressions = [];
		foreach ($ourConditionalExpressions as $exprString => $holders) {
			if (!array_key_exists($exprString, $theirConditionalExpressions)) {
				continue;
			}

			$otherHolders = $theirConditionalExpressions[$exprString];
			$intersectedHolders = [];
			foreach ($holders as $key => $holder) {
				if (!array_key_exists($key, $otherHolders)) {
					continue;
				}
				$intersectedHolders[$key] = $holder;
			}

			if (count($intersectedHolders) === 0) {
				continue;
			}

			$newConditionalExpressions[$exprString] = $intersectedHolders;
		}

		return $newConditionalExpressions;
	}

	/**
	 * Mirrors the former MutatingScope::createConditionalExpressions().
	 *
	 * @param array<string, ConditionalExpressionHolder[]> $conditionalExpressions
	 * @param array<string, ExpressionTypeHolder> $ourExpressionTypes
	 * @param array<string, ExpressionTypeHolder> $theirExpressionTypes
	 * @param array<string, ExpressionTypeHolder> $mergedExpressionTypes
	 * @param array<string, true> $differingKeys
	 * @return array<string, ConditionalExpressionHolder[]>
	 */
	public static function createConditionalExpressions(
		array $conditionalExpressions,
		array $ourExpressionTypes,
		array $theirExpressionTypes,
		array $mergedExpressionTypes,
		array $differingKeys,
	): array
	{
		$newVariableTypes = $ourExpressionTypes;

		// When our-branch type is a subtype of their-branch type, the union
		// absorbs it (merged === their). Such a variable is a poor *guard* —
		// asserting its our-branch type later wouldn't reliably select this
		// branch — but it remains a valid conditional *target*, so only exclude
		// it from guard selection instead of dropping it entirely.
		$guardsToExclude = [];
		foreach (array_keys($differingKeys) as $exprString) {
			if (!array_key_exists($exprString, $theirExpressionTypes)) {
				continue;
			}
			$holder = $theirExpressionTypes[$exprString];
			if (!array_key_exists($exprString, $mergedExpressionTypes)) {
				continue;
			}

			if (!$mergedExpressionTypes[$exprString]->equalTypes($holder)) {
				continue;
			}

			if (
				array_key_exists($exprString, $newVariableTypes)
				&& !$newVariableTypes[$exprString]->getCertainty()->equals($holder->getCertainty())
				&& $newVariableTypes[$exprString]->equalTypes($holder)
			) {
				continue;
			}

			$guardsToExclude[$exprString] = true;
		}

		$typeGuards = [];
		foreach (array_keys($differingKeys) as $exprString) {
			if (!array_key_exists($exprString, $newVariableTypes)) {
				continue;
			}
			$holder = $newVariableTypes[$exprString];
			if ($holder->getExpr() instanceof VirtualNode) {
				continue;
			}
			if (!array_key_exists($exprString, $mergedExpressionTypes)) {
				continue;
			}
			if (!$holder->getCertainty()->yes()) {
				continue;
			}
			if (array_key_exists($exprString, $guardsToExclude)) {
				continue;
			}

			if (
				array_key_exists($exprString, $theirExpressionTypes)
				&& !$theirExpressionTypes[$exprString]->getCertainty()->yes()
			) {
				continue;
			}

			if ($mergedExpressionTypes[$exprString]->equalTypes($holder)) {
				continue;
			}

			$typeGuards[$exprString] = $holder;
		}

		if (count($typeGuards) === 0) {
			return $conditionalExpressions;
		}

		// Both isSuperTypeOf() checks below depend only on the guard (and its
		// their-branch type), not on the target $exprString, so their results are
		// invariant across the target loop. Cache them per guard to avoid
		// recomputing expensive supertype checks on big union / constant-array
		// types once per (target, guard) pair.
		$guardIsSuperTypeOfTheirExprCache = [];
		$theirExprIsSuperTypeOfGuardCache = [];

		foreach (array_keys($differingKeys) as $exprString) {
			if (!array_key_exists($exprString, $newVariableTypes)) {
				continue;
			}
			$holder = $newVariableTypes[$exprString];
			if ($holder->getExpr() instanceof VirtualNode) {
				continue;
			}
			if (
				array_key_exists($exprString, $mergedExpressionTypes)
				&& $mergedExpressionTypes[$exprString]->equals($holder)
			) {
				continue;
			}

			$variableTypeGuards = $typeGuards;
			unset($variableTypeGuards[$exprString]);

			if (count($variableTypeGuards) === 0) {
				continue;
			}

			$exprIsGuardExcluded = array_key_exists($exprString, $guardsToExclude);
			foreach ($variableTypeGuards as $guardExprString => $guardHolder) {
				// A subtype-absorbed target (kept only for re-narrowing) paired with a
				// constant-array guard never helps: such a guard represents a unique
				// literal value that is not re-asserted as a condition later, yet the
				// downstream isSuperTypeOf() guard machinery pays to compare these
				// (potentially huge) constant arrays on every branch merge. Skip them.
				if ($exprIsGuardExcluded && $guardHolder->getType()->isConstantArray()->yes()) {
					continue;
				}

				if (
					array_key_exists($guardExprString, $theirExpressionTypes)
					&& $theirExpressionTypes[$guardExprString]->getCertainty()->yes()
				) {
					$guardIsSuperTypeOfTheirExpr = $guardIsSuperTypeOfTheirExprCache[$guardExprString] ??= $guardHolder->getType()->isSuperTypeOf($theirExpressionTypes[$guardExprString]->getType());

					// The reverse isSuperTypeOf() check is expensive on big union /
					// constant-array types, so it is evaluated last and only when the
					// cheaper forward-based conditions did not already decide.
					if (
						$guardIsSuperTypeOfTheirExpr->yes()
						|| (
							array_key_exists($exprString, $theirExpressionTypes)
							&& $theirExpressionTypes[$exprString]->getCertainty()->yes()
							&& !$guardIsSuperTypeOfTheirExpr->no()
						)
						|| (
							!array_key_exists($exprString, $theirExpressionTypes)
							&& $holder->getType()->equals($guardHolder->getType())
							&& !$guardIsSuperTypeOfTheirExpr->no()
						)
						|| ($theirExprIsSuperTypeOfGuardCache[$guardExprString] ??= $theirExpressionTypes[$guardExprString]->getType()->isSuperTypeOf($guardHolder->getType()))->yes()
					) {
						continue;
					}
				}

				$conditionalExpression = new ConditionalExpressionHolder([$guardExprString => $guardHolder], $holder);
				$conditionalExpressions[$exprString][$conditionalExpression->getKey()] = $conditionalExpression;
			}
		}

		foreach (array_keys($differingKeys) as $exprString) {
			if (!array_key_exists($exprString, $mergedExpressionTypes)) {
				continue;
			}
			$mergedExprTypeHolder = $mergedExpressionTypes[$exprString];
			if (array_key_exists($exprString, $ourExpressionTypes)) {
				continue;
			}

			foreach ($typeGuards as $guardExprString => $guardHolder) {
				$conditionalExpression = new ConditionalExpressionHolder([$guardExprString => $guardHolder], new ExpressionTypeHolder($mergedExprTypeHolder->getExpr(), new ErrorType(), TrinaryLogic::createNo()));
				$conditionalExpressions[$exprString][$conditionalExpression->getKey()] = $conditionalExpression;
			}
		}

		return $conditionalExpressions;
	}

	/**
	 * The scan of MutatingScope::invalidateMethodsOnExpression(): drops tracked
	 * MethodCall expressions whose var matches the invalidated key, or returns
	 * null when nothing changed.
	 *
	 * @param array<string, ExpressionTypeHolder> $expressionTypes
	 * @param array<string, ExpressionTypeHolder> $nativeExpressionTypes
	 * @return array{array<string, ExpressionTypeHolder>, array<string, ExpressionTypeHolder>}|null
	 */
	public static function invalidateMethodsOnExpression(
		ExprPrinter $exprPrinter,
		string $exprStringToInvalidate,
		array $expressionTypes,
		array $nativeExpressionTypes,
	): ?array
	{
		$invalidated = false;
		foreach ($expressionTypes as $exprString => $exprTypeHolder) {
			$expr = $exprTypeHolder->getExpr();
			if (!$expr instanceof MethodCall) {
				continue;
			}

			if (self::nodeKey($expr->var, $exprPrinter) !== $exprStringToInvalidate) {
				continue;
			}

			unset($expressionTypes[$exprString]);
			unset($nativeExpressionTypes[$exprString]);
			$invalidated = true;
		}

		if (!$invalidated) {
			return null;
		}

		return [$expressionTypes, $nativeExpressionTypes];
	}

	public static function getIntertwinedRefRootVariableName(Expr $expr): ?string
	{
		if ($expr instanceof Variable && is_string($expr->name)) {
			return $expr->name;
		}
		if ($expr instanceof Expr\ArrayDimFetch) {
			return self::getIntertwinedRefRootVariableName($expr->var);
		}
		return null;
	}

	/**
	 * The conditional-expressions fixed-point matching of
	 * MutatingScope::filterBySpecifiedTypes().
	 *
	 * @param array<string, ConditionalExpressionHolder[]> $conditionalExpressions
	 * @param array<string, ExpressionTypeHolder> $specifiedExpressions
	 * @return array{array<string, ConditionalExpressionHolder[]>, array<string, ExpressionTypeHolder>}
	 */
	public static function matchConditionalExpressions(array $conditionalExpressions, array $specifiedExpressions): array
	{
		$conditions = [];
		$originallySpecifiedExprStrings = $specifiedExpressions;
		$prevSpecifiedCount = -1;
		while (count($specifiedExpressions) !== $prevSpecifiedCount) {
			$prevSpecifiedCount = count($specifiedExpressions);
			foreach ($conditionalExpressions as $conditionalExprString => $conditionalExpressionHolders) {
				if (array_key_exists($conditionalExprString, $conditions)) {
					continue;
				}

				// Pass 1: Prefer exact matches
				foreach ($conditionalExpressionHolders as $conditionalExpression) {
					if (
						$conditionalExpression->getTypeHolder()->getCertainty()->no()
						&& array_key_exists($conditionalExprString, $originallySpecifiedExprStrings)
					) {
						continue;
					}
					foreach ($conditionalExpression->getConditionExpressionTypeHolders() as $holderExprString => $conditionalTypeHolder) {
						if (
							!array_key_exists($holderExprString, $specifiedExpressions)
							|| !$conditionalTypeHolder->equals($specifiedExpressions[$holderExprString])
						) {
							continue 2;
						}
					}

					$conditions[$conditionalExprString][] = $conditionalExpression;
					$specifiedExpressions[$conditionalExprString] = $conditionalExpression->getTypeHolder();
				}

				if (array_key_exists($conditionalExprString, $conditions)) {
					continue;
				}

				// Pass 2: Supertype match. Only runs when Pass 1 found no exact match for this expression.
				foreach ($conditionalExpressionHolders as $conditionalExpression) {
					if ($conditionalExpression->getTypeHolder()->getCertainty()->no()) {
						continue;
					}
					foreach ($conditionalExpression->getConditionExpressionTypeHolders() as $holderExprString => $conditionalTypeHolder) {
						if (
							!array_key_exists($holderExprString, $specifiedExpressions)
							|| !$conditionalTypeHolder->getCertainty()->equals($specifiedExpressions[$holderExprString]->getCertainty())
							|| !$conditionalTypeHolder->getType()->isSuperTypeOf($specifiedExpressions[$holderExprString]->getType())->yes()
						) {
							continue 2;
						}
					}

					$conditions[$conditionalExprString][] = $conditionalExpression;
					$specifiedExpressions[$conditionalExprString] = $conditionalExpression->getTypeHolder();
				}
			}
		}

		return [$conditions, $specifiedExpressions];
	}

}
