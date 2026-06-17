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
	 * typeCallback now that this handler no longer implements
	 * TypeResolvingExprHandler.
	 *
	 * @return Closure(MutatingScope): Type
	 */
	public static function createTypeCallback(Variable $expr, ?ExpressionResult $nameResult = null): Closure
	{
		return static function (MutatingScope $s) use ($expr, $nameResult): Type {
			if (is_string($expr->name)) {
				if ($s->hasVariableType($expr->name)->no()) {
					return new ErrorType();
				}

				return $s->getVariableType($expr->name);
			}

			$nameType = $nameResult !== null
				? $nameResult->getTypeForScope($s)
				: $s->getType($expr->name);
			if (count($nameType->getConstantStrings()) > 0) {
				$types = [];
				foreach ($nameType->getConstantStrings() as $constantString) {
					$variableScope = $s
						->filterByTruthyValue(
							new Identical($expr->name, new String_($constantString->getValue())),
						);
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
			typeCallback: self::createTypeCallback($expr, $nameResult),
			specifyTypesCallback: fn (MutatingScope $s, TypeSpecifierContext $context): SpecifiedTypes => $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context),
		);
	}

}
