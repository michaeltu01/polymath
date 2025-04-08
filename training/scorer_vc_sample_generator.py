# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from asyncio import Lock, run
from json import dumps
from logging import getLogger, Logger
from os import path
from typing import Any, Optional

from agent.logic.logic_py_c_harness_generator import LogicPyCHarnessGenerator

from aiofiles import open

from aiofiles.threadpool.text import AsyncTextIOWrapper
from concurrency.async_pool import AsyncPool
from dotenv import load_dotenv
from inference.chat_completion import Message
from libcst import Module, parse_module
from training.cbmc_scorer_vc_factory import CBMCScorerVerificationConstraintsFactory
from training.logic_rl_training_dialog import LogicRlTrainingDialog
from training.sample_output_converter import SampleOutputConverter
from training.sample_output_converter_factory import create_sample_output_converter
from training.scorer_vc_sample_parser import ScorerVCSampleParser
from training.scorer_vc_sample_parser_factory import create_scorer_vc_sample_parser


class ScorerVcSampleGenerator:
    """
    Helper script to convert a batch of samples that can be converted to
    Logic.py data structures and constraints to Scorer VC RL training data.
    Ideally, Scorer VC RL training data is generated directly alongside the
    sample itself being generated, e.g. generating data structures and
    constraints at the same time as generating a Zebra puzzle. This converter
    is intended for scenarios where we would like to generate the constraints
    after the fact, e.g. parsing them from the sample.
    """

    def __init__(self) -> None:
        self.__logger: Logger = getLogger(__name__)
        self.__logging_lock = Lock()
        self.__output_file_lock = Lock()
        self.__constraint_factory = CBMCScorerVerificationConstraintsFactory(
            lambda _: self.__logger
        )
        self.__parser: ScorerVCSampleParser = create_scorer_vc_sample_parser()
        self.__sample_output_converter: SampleOutputConverter = (
            create_sample_output_converter()
        )

    async def process(self, input_file_path: str, output_file_path: str) -> None:
        """
        Amends the sample in the input file by scorer VC added to the output
        file.

        Args:
            input_file_path (str): Input samples to amend with scorer VC.
            output_file_path (str): Output samples suitabe for scorer VC RL
            training.
        """
        pool = AsyncPool(100)
        async with open(output_file_path, "w") as output_file:
            async with open(input_file_path, "r") as input_file:
                async for line in input_file:
                    await pool.submit(
                        lambda line=line: self.process_line(output_file, line)
                    )
                await pool.gather()

    async def process_line(self, output_file: AsyncTextIOWrapper, line: str) -> None:
        """
        Generates scorer VC for a single input sample.

        Args:
            output_file (AsyncTextIOWrapper): Output file to which to write
            result sample.
            line (str): Input sample to convert.
        """
        puzzle: str
        data_structure: str
        constraints: str
        try:
            puzzle, data_structure, constraints = self.__parser.parse(line)
        except Exception:
            async with self.__logging_lock:
                self.__logger.exception(f"Invalid puzzle: {line}")
            return

        python_code: str = f"""{data_structure}

{constraints}
"""
        module: Module = parse_module(python_code)
        c_code: str = LogicPyCHarnessGenerator.generate(module)

        scorer_vc: Optional[str] = await self.__constraint_factory.convert(c_code)
        if scorer_vc is None:
            raise ValueError(f"Failed to convert sample: {line}")
        dialog: list[Message] = LogicRlTrainingDialog.create(puzzle, data_structure)
        metadata: dict[str, Any] = {"scorer_vc": scorer_vc}
        sample: Any = self.__sample_output_converter.convert(dialog, metadata)
        output_line: str = f"{dumps(sample)}\n"

        async with self.__output_file_lock:
            await output_file.write(output_line)


async def main() -> None:
    load_dotenv()
    module_path: str = path.dirname(__file__)
    base_path: str = path.join(module_path, "../../datasets")
    # Set input and output file names
    input_file: str = path.join(base_path, "zebra-in.jsonl")
    output_file: str = path.join(base_path, "zebra-out.jsonl")
    generator = ScorerVcSampleGenerator()
    await generator.process(input_file, output_file)


if __name__ == "__main__":
    run(main())
