<?php declare(strict_types = 1);

namespace PHPStan\Analyser\ExprHandler;

use PhpParser\Node\Expr;
use PhpParser\Node\Expr\PreInc;
use PhpParser\Node\Scalar\Int_;
use PhpParser\Node\Stmt;
use PHPStan\Analyser\ExpressionContext;
use PHPStan\Analyser\ExpressionResult;
use PHPStan\Analyser\ExpressionResultFactory;
use PHPStan\Analyser\ExpressionResultStorage;
use PHPStan\Analyser\ExprHandler;
use PHPStan\Analyser\ExprHandler\Helper\DefaultNarrowingHelper;
use PHPStan\Analyser\MutatingScope;
use PHPStan\Analyser\NodeScopeResolver;
use PHPStan\Analyser\SpecifiedTypes;
use PHPStan\Analyser\TypeSpecifierContext;
use PHPStan\DependencyInjection\AutowiredService;
use PHPStan\Reflection\InitializerExprTypeResolver;
use PHPStan\ShouldNotHappenException;
use PHPStan\Type\Accessory\AccessoryLiteralStringType;
use PHPStan\Type\BenevolentUnionType;
use PHPStan\Type\Constant\ConstantIntegerType;
use PHPStan\Type\ConstantTypeHelper;
use PHPStan\Type\FloatType;
use PHPStan\Type\IntegerType;
use PHPStan\Type\IntersectionType;
use PHPStan\Type\NeverType;
use PHPStan\Type\StringType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use ValueError;
use function count;
use function is_bool;
use function is_numeric;
use function is_string;
use function str_increment;

/**
 * @implements ExprHandler<PreInc>
 */
#[AutowiredService]
final class PreIncHandler implements ExprHandler
{

	public function __construct(
		private ExpressionResultFactory $expressionResultFactory,
		private InitializerExprTypeResolver $initializerExprTypeResolver,
		private DefaultNarrowingHelper $defaultNarrowingHelper,
	)
	{
	}

	public function supports(Expr $expr): bool
	{
		return $expr instanceof PreInc;
	}

	public function processExpr(NodeScopeResolver $nodeScopeResolver, Stmt $stmt, Expr $expr, MutatingScope $scope, ExpressionResultStorage $storage, callable $nodeCallback, ExpressionContext $context): ExpressionResult
	{
		$varResult = $nodeScopeResolver->processExprNode($stmt, $expr->var, $scope, $storage, $nodeCallback, $context->enterDeep());

		$typeCallback = function (bool $nativeTypesPromoted) use ($expr, $varResult): Type {
			$varType = ($nativeTypesPromoted ? $varResult->getNativeType() : $varResult->getType());
			$varScalars = $varType->getConstantScalarValues();

			if (count($varScalars) > 0) {
				$newTypes = [];

				foreach ($varScalars as $varValue) {
					if ($varValue === '') {
						$varValue = '1';
					} elseif (is_string($varValue) && !is_numeric($varValue)) {
						try {
							$varValue = str_increment($varValue);
						} catch (ValueError) {
							return new NeverType();
						}
					} elseif (!is_bool($varValue)) {
						++$varValue;
					}

					$newTypes[] = ConstantTypeHelper::getTypeFromValue($varValue);
				}
				return TypeCombinator::union(...$newTypes);
			} elseif ($varType->isString()->yes()) {
				if ($varType->isLiteralString()->yes()) {
					return new IntersectionType([
						new StringType(),
						new AccessoryLiteralStringType(),
					]);
				}

				if ($varType->isNumericString()->yes()) {
					return new BenevolentUnionType([
						new IntegerType(),
						new FloatType(),
					]);
				}

				return new BenevolentUnionType([
					new StringType(),
					new IntegerType(),
					new FloatType(),
				]);
			}

			$one = new Int_(1);
			return $this->initializerExprTypeResolver->getPlusType($expr->var, $one, static function (Expr $e) use ($nativeTypesPromoted, $expr, $varResult, $one): Type {
				if ($e === $expr->var) {
					return ($nativeTypesPromoted ? $varResult->getNativeType() : $varResult->getType());
				}
				if ($e === $one) {
					return new ConstantIntegerType(1);
				}

				throw new ShouldNotHappenException();
			});
		};
		$specifyTypesCallback = fn (MutatingScope $s, TypeSpecifierContext $context): SpecifiedTypes => $this->defaultNarrowingHelper->specifyDefaultTypes($expr, $context);

		// processVirtualAssign asks getType($expr) for the value to assign; store
		// this result first so that resolves from the typeCallback below rather
		// than re-processing the node on demand (which would recurse).
		$nodeScopeResolver->storeExpressionResult($storage, $expr, $this->expressionResultFactory->create(
			$varResult->getScope(),
			beforeScope: $scope,
			expr: $expr,
			hasYield: $varResult->hasYield(),
			isAlwaysTerminating: $varResult->isAlwaysTerminating(),
			throwPoints: $varResult->getThrowPoints(),
			impurePoints: $varResult->getImpurePoints(),
			typeCallback: $typeCallback,
			specifyTypesCallback: $specifyTypesCallback,
		));

		return $this->expressionResultFactory->create(
			$nodeScopeResolver->processVirtualAssign(
				$varResult->getScope(),
				$storage,
				$stmt,
				$expr->var,
				$expr,
				$nodeCallback,
			)->getScope(),
			beforeScope: $scope,
			expr: $expr,
			hasYield: $varResult->hasYield(),
			isAlwaysTerminating: $varResult->isAlwaysTerminating(),
			throwPoints: $varResult->getThrowPoints(),
			impurePoints: $varResult->getImpurePoints(),
			typeCallback: $typeCallback,
			specifyTypesCallback: $specifyTypesCallback,
		);
	}

}
