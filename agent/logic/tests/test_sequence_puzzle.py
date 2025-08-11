from io import StringIO
from json import loads
from re import compile, DOTALL, Match, Pattern
from typing import Any, Optional
from unittest import IsolatedAsyncioTestCase

from agent.logic.agent import LogicAgent
from agent.logic.cbmc_search_engine_strategy import CBMCSearchEngineStrategy
from agent.logic.engine_strategy import EngineStrategy

from dotenv import load_dotenv
from inference.chat_completion_factory import create_chat_completion
from judge.result_trace import ResultTrace
from logger.logger_factory import LoggerFactory


load_dotenv()


class TestSequencePuzzle(IsolatedAsyncioTestCase):

    def __init__(self, methodName="runTest") -> None:
        super().__init__(methodName)
        self.maxDiff = None

    async def test_solve(self) -> None:
        puzzle: str = """This is an arithmetic sequence puzzle. Fill in the missing variables such that each line forms a sequence of numbers, where the arithmetic difference between two numbers in the same line is the same.

A, B, 21
A, 7, C, 15
D, C, E, 21
"""
        output_format: str = """Create a JSON object that adheres to the following schema:

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "type": "object",
  "properties": {
    "A": { "type": "integer" },
    "B": { "type": "integer" },
    "C": { "type": "integer" },
    "D": { "type": "integer" },
    "E": { "type": "integer" }
  },
  "required": ["A", "B", "C", "D", "E"]
}
```
"""

        result_trace = ResultTrace("0")
        log_stream = StringIO()
        with LoggerFactory(log_stream, True) as logger_factory:
            engine_strategy: EngineStrategy = CBMCSearchEngineStrategy(
                logger_factory, puzzle, output_format
            )
            async with create_chat_completion(
                logger_factory, "llama3-70b-instruct"
            ) as chat_completion:
                solver = LogicAgent(
                    logger_factory, chat_completion, engine_strategy, result_trace
                )
                await solver.solve()

        solution: Optional[str] = result_trace.solution
        assert solution is not None
        json_object: Pattern = compile(r".*(\{.*\}).*", DOTALL)
        json_match: Optional[Match] = json_object.match(solution)
        assert json_match is not None
        result_text: str = json_match.group(1)
        result: Any = loads(result_text)
        assert result == {"A": 3, "B": 12, "C": 11, "D": 6, "E": 16}
