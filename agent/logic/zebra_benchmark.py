# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

import asyncio
import os
from io import StringIO
from json import dumps
from typing import Any, Callable, Tuple

import aiofiles

from agent.logic.agent import LogicAgent, ResultTrace
from agent.logic.cbmc_search_engine_strategy import CBMCSearchEngineStrategy
from agent.logic.engine_strategy import EngineStrategy
from concurrency.async_pool import AsyncPool

from dotenv import load_dotenv
from inference.chat_completion_factory import create_chat_completion
from logger.logger_factory import LoggerFactory
from pyarrow import Table
from pyarrow.parquet import ParquetFile


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
        self.__eval_json_file_name: str = eval_json_file_name
        self.__generator: str = generator
        self.__model_name: str = model_name
        self.__enable_stderr_log: bool = enable_stderr_log
        self.__filter_dataset: Callable[[dict[str, Any]], bool] = filter_dataset

        module_path: str = os.path.dirname(__file__)
        self.__zebra_input_dataset_path: str = os.path.join(
            module_path, "../../datasets/grid_mode/test-00000-of-00001.parquet"
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

        async with aiofiles.open(self.__eval_json_file_name, "w") as file:
            await file.write(dumps(eval_json, indent=4))

    async def run_task(
        self, eval_json: list[dict[str, Any]], task: dict[str, Any]
    ) -> None:
        """
        Executes a single benchmark task and stores the result in `eval_json`.
        """
        puzzle: str = task["puzzle"]
        output_format: str = ZebraBenchmark.get_format(task["solution"])

        log_stream = StringIO()
        result_trace = ResultTrace()
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

        eval_json.append(
            {
                "session_id": task["id"],
                "chat_history": [message["text"] for message in result_trace.messages],
                "model_input": "n/a",
                "output": [result_trace.solution],
                "debug_output": [f"{log_stream.getvalue()}\n{repr(result_trace)}"],
                "generator": self.__generator,
                "configs": {},
                "dataset": "zebra-grid",
                "id": task["id"],
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
        benchmark = ZebraBenchmark(model[0], model[1], model[2])
        await benchmark.run()


if __name__ == "__main__":
    asyncio.run(main())
