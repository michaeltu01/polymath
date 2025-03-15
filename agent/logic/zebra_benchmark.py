# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

import os
from asyncio import Lock, run
from io import StringIO
from json import dumps, loads
from logging import Logger
from re import compile, fullmatch, Match, Pattern
from types import TracebackType
from typing import Any, Callable, Optional, Tuple

import aiofiles

from agent.logic.agent import LogicAgent
from agent.logic.cbmc_search_engine_strategy import CBMCSearchEngineStrategy
from agent.logic.engine_strategy import EngineStrategy
from aiofiles.base import AiofilesContextManager
from aiofiles.threadpool.text import AsyncTextIOWrapper
from concurrency.async_pool import AsyncPool

from dotenv import load_dotenv
from inference.chat_completion import Message
from inference.chat_completion_factory import create_chat_completion
from judge.json_judge import JsonJudge
from judge.result_trace import ResultTrace
from logger.logger_factory import LoggerFactory
from pyarrow import Table
from pyarrow.parquet import ParquetFile

from training.logic_rl_training_dialog import LogicRlTrainingDialog
from training.sample_output_converter import SampleOutputConverter
from training.sample_output_converter_factory import create_sample_output_converter


_ZERO_EVAL_HOUSE_NAME_PATTERN: Pattern = compile("House ([\\d]*)")


class ZebraBenchmark:
    """
    Benchmark runner for Zebra Grid puzzles.
    """

    def __init__(
        self,
        eval_json_file_name: str,
        generator: str,
        model_name: str,
        enable_stderr_log: bool = True,
        generate_training_data: bool = False,
        filter_dataset: Callable[[dict[str, Any]], bool] = lambda task: True,
    ) -> None:
        """
        Args:
            eval_json_file_name (str): Result JSON output file.
            generator (str): Generator name used in ZebraLogic leader board.
            model_name (str): Name of model to use in inference client.
            enable_stderr_log (bool): Indicates whether log messages should be
            writting to stderr as well as the result JSON. Disabled for unit
            tests.
            filter_dataset (Callable[[Any], Any]): Filter to select which tasks
            from the benchmark set to run.
        """
        self.__eval_json_file_name = eval_json_file_name
        self.__xlformers_output_dataset_lock = Lock()
        self.__generator: str = generator
        self.__model_name: str = model_name
        self.__enable_stderr_log: bool = enable_stderr_log
        self.__filter_dataset: Callable[[dict[str, Any]], bool] = filter_dataset
        self.__xlformers_output_dataset_context: Optional[AiofilesContextManager] = (
            aiofiles.open(
                self.__eval_json_file_name.replace(".json", "-dataset.json"), "w"
            )
            if generate_training_data
            else None
        )
        self.__judge: Callable[[ResultTrace, Any], bool] = JsonJudge()
        self.__sample_output_converter: SampleOutputConverter = (
            create_sample_output_converter()
        )

        module_path: str = os.path.dirname(__file__)
        self.__zebra_input_dataset_path: str = os.path.join(
            module_path, "../../datasets/grid_mode/test-00000-of-00001.parquet"
        )

    async def __aenter__(self) -> "ZebraBenchmark":
        if self.__xlformers_output_dataset_context:
            self.__xlformers_output_dataset: AsyncTextIOWrapper = (
                await self.__xlformers_output_dataset_context.__aenter__()
            )
        return self

    async def __aexit__(
        self,
        exc_type: Optional[type[BaseException]],
        exc_value: Optional[BaseException],
        exc_tb: Optional[TracebackType],
    ) -> None:
        if self.__xlformers_output_dataset_context:
            await self.__xlformers_output_dataset_context.__aexit__(
                exc_type, exc_value, exc_tb
            )

    async def run(self) -> None:
        """
        Runs all Zebra puzzles specified in the input dataset JSON file.
        """
        pool = AsyncPool(100)
        eval_json: list[dict[str, Any]] = []
        dataset = ParquetFile(self.__zebra_input_dataset_path)
        for row_group_index in range(dataset.num_row_groups):
            table: Table = dataset.read_row_group(row_group_index)
            rows: list[dict[str, Any]] = table.to_pylist()
            for task in rows:
                if self.__filter_dataset(task):
                    pool.submit(lambda task=task: self.run_task(eval_json, task))

        await pool.gather()

        if self.__xlformers_output_dataset_context:
            # TODO: Write RL scorer metadata
            pass
        else:
            async with aiofiles.open(self.__eval_json_file_name, "w") as file:
                await file.write(dumps(eval_json, indent=4))

    async def run_task(
        self,
        eval_json: list[dict[str, Any]],
        task: dict[str, Any],
    ) -> None:
        """
        Executes a single benchmark task and stores the result in `eval_json`.
        """
        task_id: str = task["id"]
        puzzle: str = task["puzzle"]
        expected_solution: Any = task["solution"]
        output_format: str = ZebraBenchmark.get_format(expected_solution)

        log_stream = StringIO()
        result_trace = ResultTrace(task_id)
        with LoggerFactory(log_stream, self.__enable_stderr_log) as logger_factory:
            engine_strategy: EngineStrategy = CBMCSearchEngineStrategy(
                logger_factory, puzzle, output_format
            )
            async with create_chat_completion(
                logger_factory, self.__model_name
            ) as chat_completion:
                agent = LogicAgent(
                    logger_factory, chat_completion, engine_strategy, result_trace
                )
                await agent.solve()

            logger: Logger = logger_factory(__name__)
            if self.__xlformers_output_dataset_context:
                hugging_face_solution: Optional[Any] = (
                    ZebraBenchmark.convert_to_reference_solution_format(
                        result_trace.solution
                    )
                )
                if hugging_face_solution != expected_solution:
                    logger.warning(
                        f"""Discarding task `{task_id}` due to incorrect solution.
Expected:
```
{dumps(expected_solution)}
```
Actual:
```
{dumps(result_trace.solution)}
```
"""
                    )
                elif not result_trace.python_data_structure:
                    logger.error(
                        f"Discarding task `{task_id}` due to missing data structure."
                    )
                else:
                    # TODO: Produce VC GOTO binary
                    dialog: list[Message] = LogicRlTrainingDialog.create(
                        puzzle, result_trace.python_data_structure
                    )
                    sample: Any = self.__sample_output_converter.convert(dialog, {})
                    lines: list[str] = [dumps(sample)]
                    async with self.__xlformers_output_dataset_lock:
                        await self.__xlformers_output_dataset.writelines(lines)

        if not self.__xlformers_output_dataset_context:
            eval_json.append(
                {
                    "session_id": task_id,
                    "chat_history": [message.text for message in result_trace.messages],
                    "model_input": "n/a",
                    "output": [result_trace.solution],
                    "debug_output": [f"{log_stream.getvalue()}\n{repr(result_trace)}"],
                    "generator": self.__generator,
                    "configs": {},
                    "dataset": "zebra-grid",
                    "id": task_id,
                    "size": task["size"],
                    "puzzle": puzzle,
                    "created_at": task["created_at"],
                }
            )

    @staticmethod
    def get_format(solution_placeholder: dict[str, Any]) -> str:
        """
        Converts a solution placeholder from the Zebra dataset to the correct
        template of the expected output format to pass to the model.
        """
        num_houses: int = len(solution_placeholder["rows"])
        headers: list[str] = solution_placeholder["header"]
        house_prefix: str = headers[0]
        solution_format: dict[str, dict[str, str]] = {}
        for house_number in range(1, num_houses + 1):
            house_format: dict[str, str] = {}
            for header in headers[1:]:
                house_format[header] = "___"
            solution_format[f"{house_prefix} {house_number}"] = house_format

        solution_container: dict[str, dict[str, dict[str, str]]] = {}
        solution_container["solution"] = solution_format
        return dumps(solution_container, indent=4)

    @staticmethod
    def convert_to_reference_solution_format(solution: Optional[str]) -> Optional[Any]:
        """
        ZebraLogicBench has two solution formats: The HuggingFace dataset is
        formatted in what we call the "reference" solution format, and the
        ZeroEval benchmark evaluation tool accepts another format. This class
        produces the latter, since we need to evaluate using ZeroEval. However,
        when checking whether our scorer VCs are correct, we compare against the
        ground truth in the HuggingFace dataset directly. To do so, we use this
        function to convert the ZeroEval solution.

        Args:
            solution (str): Solution in ZeroEval format.
        Returns:
            solution in HuggingFace ZebraLogicBench format.
        """
        if not solution:
            return None

        header: list[str] = ["House"]
        is_first_house: bool = True
        zero_eval_solution: Any = loads(solution)["solution"]
        num_houses: int = len(zero_eval_solution)
        rows: list[list[str]] = [[] for _ in range(num_houses)]
        for house_name, house in zero_eval_solution.items():
            parsed: Optional[Match] = fullmatch(
                _ZERO_EVAL_HOUSE_NAME_PATTERN, house_name
            )
            if not parsed:
                return None

            house_number: str = parsed.group(1)
            house_index: int = int(house_number) - 1
            row: list[str] = rows[house_index]
            row.append(house_number)
            for name, value in house.items():
                row.append(value)
                if is_first_house:
                    header.append(name)
            is_first_house = False
        return {
            "header": header,
            "rows": rows,
        }


async def main():
    load_dotenv()
    module_path: str = os.path.dirname(__file__)
    base_path: str = os.path.abspath(
        os.path.join(module_path, "../../lib/ZeroEval/result_dirs/zebra-grid/")
    )
    models: list[Tuple[str, str, str]] = [
        (
            os.path.join(base_path, "Meta-Llama-3.1-70B-Instruct@reasoning.json"),
            "meta-llama/Meta-Llama-3.1-70B-Instruct@reasoning",
            "llama3.1-70b-instruct",
        ),
    ]
    for model in models:
        async with ZebraBenchmark(
            model[0],
            model[1],
            model[2],
        ) as benchmark:
            await benchmark.run()


if __name__ == "__main__":
    run(main())
