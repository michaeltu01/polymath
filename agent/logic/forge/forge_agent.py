"""
Forge Agent

This module should implement a LogicAgent subclass that uses the Forge backend.

TODO:
- Integrate the Forge harness generator and search engine strategy.
- Implement any LogicAgent methods that need to be customized for Forge.
"""

from logging import Logger
from re import DOTALL, Match, Pattern, compile
from typing import Callable, Optional, Tuple
from agent.logic.agent import LogicAgent
from agent.logic.forge.forge_search_engine_strategy import ForgeSearchEngineStrategy
from agent.logic.engine_strategy import EngineStrategy, SolverOutcome
from libcst import MetadataWrapper, parse_module, Module
from libcst._exceptions import ParserSyntaxError
from tempfile import NamedTemporaryFile
import os

from agent.symex.module_with_type_info_factory import ModuleWithTypeInfoFactory
from concurrency.subprocess import Subprocess
from inference.chat_completion import ChatCompletion, Role
from inference.client import InferenceClient
from judge.result_trace import ResultTrace

# Sent if an expected code snippet was not found.
NO_CODE_FOUND_MESSAGE: str = """I could not find the requested output code snippet in your last message. Please make sure you mark it as follows:
```
your output code snippet
```

Please send the entire {} again."""

# Pattern extracting code snippets from a model response.
CODE_EXTRACTION_PATTERN: Pattern = compile(r".*```[^\n]*\n+(.*)```.*", DOTALL)

# Code marker pattern. We remove redundant markers when extracting code from concatenated messages due to token limits.
CODE_MARKER_PATTERN: Pattern = compile(r"```[^\n]*")

RETRY_COUNT = 3
_SOLVER_TIMEOUT = 60  # seconds

class ForgeAgent(LogicAgent):
    """
    LogicAgent subclass for the Forge backend.
    """
    def __init__(
        self,
        logger_factory: Callable[[str], Logger],
        chat_completion: ChatCompletion,
        engine_strategy: EngineStrategy,
        result_trace: ResultTrace,
        collect_pyre_type_information: bool = False,
    ) -> None:
        """
        Initialises inference client with default settings and the provided
        model name.

        Args:
            logger_factory (Callable[[str], Logger]): Logging configuration to
            use.
            model_name (str): Name of model to use in inference client.
            engine_strategy (EngineStrategy): Agent configuration (e.g. CBMC
            search or SMT conclusion check).
            result_trace (ResultTrace): Sink for debug and result output data.
            collect_pyre_type_information (bool): Whether libCST modules should
            be parsed with type information. This incurs a performance overhead,
            but is necessary for the Z3 back-end.
        """
        self.__logger: Logger = logger_factory(__name__)
        self.__engine_strategy: EngineStrategy = engine_strategy
        self.__client = InferenceClient(logger_factory, chat_completion)
        self.__result_trace: ResultTrace = result_trace
        self.__collect_pyre_type_information: bool = collect_pyre_type_information

    # TODO: Override methods as needed for Forge-specific logic
    async def solve(self):
        attempt: int = 0
        while True:
            attempt_failed: bool
            try:
                attempt_failed = await self.__solve()
            except:
                self.__logger.exception(
                    f"""Unexpected error during solve.
Python Code:
{self.__result_trace.python_code}

Constraints:
{self.__result_trace.solver_constraints}
"""
                )
                attempt_failed = True

            self.__result_trace.messages.extend(self.__client.conversation)
            if not attempt_failed:
                break

            self.__client.conversation.clear()
            attempt += 1
            if attempt >= RETRY_COUNT:
                break
            self.__logger.warning("Retrying solution finding due to recoverable error.")
            self.__result_trace.num_agent_retries += 1
    
    async def __solve(self) -> bool:
        """
        Retryable solution attempt. Includes data structure and constraints
        generation, CBMC invocation, CBMC output parsing, and solution
        formatting.

        Returns: `True` if the solution attempt failed due to a flaky error
        that is unlikely to repeat, e.g. syntax errors due to token limits
        spreading Python code across mutltiple messages.
        """
        data_structure: Optional[str] = await self.__generate_data_structure()
        if not data_structure:
            return False

        solution, retry_if_failed = await self.__generate_and_verify_constraints(
            data_structure
        )
        if not solution:
            return retry_if_failed

        # await self.__format_solution(solution)
        return False

    async def __generate_data_structure(self) -> Optional[str]:
        """
        Prompts the model to generate the data structure which can contain a
        solution to the puzzle.

        Returns:
            Python data structure that can contain puzzle solutions.
        """
        self.__client.add_message(self.__engine_strategy.system_prompt, Role.SYSTEM)
        self.__client.add_message(
            self.__engine_strategy.data_structure_prompt, Role.USER
        )
        data_structure: Optional[str] = await self.__receive_code_response(
            "data structure"
        )
        if data_structure:
            self.__result_trace.python_data_structure = data_structure
            print(self.__result_trace.python_data_structure)
            return data_structure
        self.__logger.error("Failed to define solution data structure.")
        return None

    async def __generate_and_verify_constraints(
        self, data_structure: str
    ) -> Tuple[Optional[str], bool]:
        """
        Prompts the model to generate the constraints describing a valid
        solution, then generates a matching solution using CBMC.
        Args:
            data_structure (str): Python data structure for solution type.
        Returns:
            First tuple element will be the solution in the solver's format, if
            it could be successfully generated, otherwise `None`. The second
            tuple element indicates whether we should retry the data structure
            and constraint generation from scratch. This can be useful if the
            model generated Python code with syntax errors.
        """
        attempts: int = 0
        while True:
            all_constraints: list[str] = []
            for constraints_prompt in self.__engine_strategy.constraints_prompt:
                self.__client.add_message(constraints_prompt, Role.USER)
                constraints: Optional[str] = await self.__receive_code_response(
                    "validation function"
                )
                if constraints is None:
                    self.__logger.error("Failed to define solution constraints.")
                    self.__result_trace.python_code = data_structure
                    return None, False
                all_constraints.append(constraints)

            python_code: str = f"""
{self.__engine_strategy.python_code_prefix}
{data_structure}
{os.linesep.join(all_constraints)}
"""
            self.__result_trace.python_code = python_code

            print(self.__result_trace.python_code)

            module: Module
            metadata: Optional[MetadataWrapper]
            try:
                if self.__collect_pyre_type_information:
                    metadata = await ModuleWithTypeInfoFactory.create_module(
                        python_code
                    )
                    module = metadata.module
                else:
                    module = parse_module(python_code)
                    metadata = None
            except ParserSyntaxError:
                self.__logger.exception("Parser error when reading constraint")
                self.__result_trace.num_logic_py_syntax_errors += 1
                return None, True

            solver_constraints: str = (
                await self.__engine_strategy.generate_solver_constraints(
                    module, metadata
                )
            )
            self.__result_trace.solver_constraints = solver_constraints

            return None, False

            solver_input_file_suffix: str = (
                self.__engine_strategy.solver_input_file_suffix
            )
            solver_exit_code: int
            stdout: str
            stderr: str
            async with NamedTemporaryFile(
                mode="w", suffix=solver_input_file_suffix, delete_on_close=False
            ) as file:
                await file.write(solver_constraints)
                await file.close()

                solver_input_file: str = str(file.name)
                try:
                    solver_exit_code, stdout, stderr = await Subprocess.run(
                        *self.__engine_strategy.generate_solver_invocation_command(
                            solver_input_file
                        ),
                        timeout_in_s=_SOLVER_TIMEOUT,
                    )
                except TimeoutError:
                    self.__logger.exception(
                        f"""Solver timeout.
Python Code:
{self.__result_trace.python_code}

Constraints:
{self.__result_trace.solver_constraints}
"""
                    )
                    self.__result_trace.num_solver_timeouts += 1
                    return None, True

            self.__result_trace.solver_output = f"{stdout}{stderr}"
            self.__result_trace.solver_exit_code = solver_exit_code

            solver_outcome, output = self.__engine_strategy.parse_solver_output(
                solver_exit_code, stdout, stderr
            )
            match solver_outcome:
                case SolverOutcome.SUCCESS:
                    return output, False
                case SolverOutcome.FATAL:
                    self.__result_trace.num_solver_errors += 1
                    return None, True
                case SolverOutcome.RETRY:
                    attempts += 1
                    if attempts >= RETRY_COUNT:
                        self.__logger.error(
                            "Exceeded retry limit for repairing constraints, giving up."
                        )
                        return None, False

                    self.__result_trace.num_solver_retries += 1
                    self.__client.add_message(
                        self.__engine_strategy.retry_prompt, Role.USER
                    )
    
    async def __receive_code_response(
        self, expected_content_description: str
    ) -> Optional[str]:
        """
        Submits the conversation, and attempts to extract a code snippet from
        the response. Will send a retry message a limited number of times if no
        code snippet was found in the response.

        Args:
            expected_content_description (str): If no code snippet was found, we
            use this description in the retry message. An example would be "data
            structure", where we would tell the model that no "data structure
            code snippet" was found and that it should regenerate it.
        Returns:
            A code snippet response from the model, if found within the retry
            limit.
        """
        attempt: int = 0
        while True:
            response_text: Optional[str] = await self.__client.send()
            if response_text is None:
                return None

            code: Optional[str] = ForgeAgent.__extract_code(response_text)
            if code:
                return code

            attempt += 1
            if attempt >= RETRY_COUNT:
                return None
            self.__client.add_message(
                NO_CODE_FOUND_MESSAGE.format(expected_content_description), Role.USER
            )

    @staticmethod
    def __extract_code(response_text: str) -> Optional[str]:
        """
        Extracts code marked with ``` prefix and suffix from a message.

        Args:
            response_text (str): Model response text containing code to extract,
            potentially surrounded by unrelated description text by the model.
        Returns:
            Single code snippet extracted from the response text.
        """
        num_code_markers: int = len(CODE_MARKER_PATTERN.findall(response_text))
        if num_code_markers > 2:
            code_marker: Optional[Match] = CODE_MARKER_PATTERN.search(response_text, 0)
            if code_marker:
                pos: int = code_marker.start() + 1
                for _ in range(2, num_code_markers):
                    code_marker = CODE_MARKER_PATTERN.search(response_text, pos)
                    if not code_marker:
                        break

                    response_text = (
                        response_text[: code_marker.start()]
                        + response_text[code_marker.end() :]
                    )
                    pos = code_marker.start() + 1

        groups: Optional[Match] = CODE_EXTRACTION_PATTERN.match(response_text)
        return groups.group(1) if groups is not None else None