<?php declare(strict_types = 1);

namespace Bug12780;

class HelloWorld
{

	public function sayHello(?int $count = null): void
	{
		$user = new \stdClass();
		$user->missedOne = [];
		$user->missedTwo = [];
		$user->missedMore = [];

		$variableName = match ($count) {
			0 => null,
			1 => 'missedOne',
			2 => 'missedTwo',
			default => 'missedMore',
		};

		if ($variableName !== null) {
			$user->$variableName['test'] ??= 0;
			$user->$variableName['test']++;

		}
	}

}
