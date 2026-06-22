<?php declare(strict_types = 1);

namespace PHPStan\Rules\Variables;

use PhpParser\Node;
use PHPStan\Analyser\Scope;
use PHPStan\DependencyInjection\RegisteredRule;
use PHPStan\Node\CoalesceExpressionNode;
use PHPStan\Rules\IssetCheck;
use PHPStan\Rules\Rule;
use PHPStan\Type\Type;

/**
 * @implements Rule<CoalesceExpressionNode>
 */
#[RegisteredRule(level: 1)]
final class NullCoalesceRule implements Rule
{

	public function __construct(private IssetCheck $issetCheck)
	{
	}

	public function getNodeType(): string
	{
		return CoalesceExpressionNode::class;
	}

	public function processNode(Node $node, Scope $scope): array
	{
		$error = $this->issetCheck->check(
			$node->getSubjectResult(),
			$scope,
			$node->getOperatorDescription(),
			'nullCoalesce',
			static function (Type $type): ?string {
				$isNull = $type->isNull();
				if ($isNull->maybe()) {
					return null;
				}

				if ($isNull->yes()) {
					return 'is always null';
				}

				return 'is not nullable';
			},
		);

		if ($error === null) {
			return [];
		}

		return [$error];
	}

}
