<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use Closure;
use PhpParser\Node\Expr;
use PhpParser\Node\Expr\BinaryOp\Identical;
use PhpParser\Node\Expr\Variable;
use PhpParser\Node\Scalar\String_;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\ImpurePoint;
use PHPStan\Analyser\IssetabilityDescriptor;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\Scope;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\ShouldNotHappenException;
use PHPStan\Type\ErrorType;
use PHPStan\Type\MixedType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use function count;
use function in_array;
use function is_string;

/**
 * @implements ExprHandler<Variable>
 */
#[AutowiredService]
final class VariableHandler implements ExprHandler
{

	public function __construct(
		private ExpressionResultFactory $expressionResultFactory,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof Variable;
	}

	/**
	 * Evaluates the variable as a read on the asking scope. Also used by
	 * AssignHandler for the placeholder result it stores for an assignment
	 * target - every stored result for a Variable node must carry a
	 * typeCallback so it can resolve its own type from the stored result.
	 *
	 * @return Closure(bool $nativeTypesPromoted): Type
	 */
	public static function createTypeCallback(Variable $expr, NodeScopeResolver $nodeScopeResolver, MutatingScope $beforeScope, ?ExpressionResult $nameResult = null): Closure
	{
		return static function (bool $nativeTypesPromoted) use ($expr, $nameResult, $nodeScopeResolver, $beforeScope): Type {
			$readScope = $nativeTypesPromoted ? $beforeScope->doNotTreatPhpDocTypesAsCertain() : $beforeScope;
			if (is_string($expr->name)) {
				if ($readScope->hasVariableType($expr->name)->no()) {
					return new ErrorType();
				}

				return $readScope->getVariableType($expr->name);
			}

			// this branch is only reached when $expr->name is an Expr, which is
			// exactly when the caller (processExpr) set $nameResult
			if ($nameResult === null) {
				throw new ShouldNotHappenException();
			}
			$nameType = $nativeTypesPromoted ? $nameResult->getNativeType() : $nameResult->getType();
			if (count($nameType->getConstantStrings()) > 0) {
				$types = [];
				foreach ($nameType->getConstantStrings() as $constantString) {
					$variableScope = $readScope->applySpecifiedTypes($nodeScopeResolver->processExprOnDemand(new Identical($expr->name, new String_($constantString->getValue())), $readScope, new ExpressionResultStorage())->getSpecifiedTypesForScope($readScope, TypeSpecifierContext::createTruthy()));
					if ($variableScope->hasVariableType($constantString->getValue())->no()) {
						$types[] = new ErrorType();
						continue;
					}

					$types[] = $variableScope->getVariableType($constantString->getValue());
				}

				return TypeCombinator::union(...$types);
			}

			return new MixedType();
		};
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$beforeScope = $scope;
		$hasYield = false;
		$throwPoints = [];
		$impurePoints = [];
		$isAlwaysTerminating = false;
		$nameResult = null;
		if (is_string($expr->name)) {
			if (in_array($expr->name, Scope::SUPERGLOBAL_VARIABLES, true)) {
				$impurePoints[] = new ImpurePoint($scope, $expr, 'superglobal', 'access to superglobal variable', true);
			}
		} else {
			$nameResult = $nodeScopeResolver->processExprNode($stmt, $expr->name, $scope, $storage, $nodeCallback, $context->enterDeep());
			$hasYield = $nameResult->hasYield();
			$throwPoints = $nameResult->getThrowPoints();
			$impurePoints = $nameResult->getImpurePoints();
			$isAlwaysTerminating = $nameResult->isAlwaysTerminating();
			$scope = $nameResult->getScope();
		}

		return $this->expressionResultFactory->create(
			$scope,
			beforeScope: $beforeScope,
			expr: $expr,
			hasYield: $hasYield,
			isAlwaysTerminating: $isAlwaysTerminating,
			throwPoints: $throwPoints,
			impurePoints: $impurePoints,
			issetabilityDescriptor: is_string($expr->name) ? IssetabilityDescriptor::variable($expr->name) : null,
			typeCallback: self::createTypeCallback($expr, $nodeScopeResolver, $beforeScope, $nameResult),
			specifyTypesCallback: fn (MutatingScope $s, TypeSpecifierContext $context): SpecifiedTypes => $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context),
		);
	}

}
