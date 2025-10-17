"""
Forge Search Engine Strategy

This module should implement the EngineStrategy interface for running Forge as a solver.

TODO:
- Implement methods to invoke the Forge solver on generated code.
- Parse Forge output and map it to Logic.py's expected result format.
- Handle errors, timeouts, and retries as needed.
"""

from collections.abc import Callable
from logging import Logger
from typing import Optional, Tuple

from libcst import MetadataWrapper, Module
from agent.logic.engine_strategy import EngineStrategy, SolverOutcome
from agent.logic.forge.logic_py_forge_harness_generator import LogicPyForgeHarnessGenerator

# Instructs the model to generate the solution constraints.
_CONSTRAINTS_MESSAGE: str = """Now you must generate a validation function which contains constraints that assert that a given solution is correct. Your solver tool will then find a solution which satisfies your constraints and thus solve the puzzle. Please adhere to the following rules:

* Express your constraints in Python, but do not use any loops or comprehensions.
* Do not generate constraints that are already enforced by the data type you selected, e.g. if a data type is marked as `Unique` you do not need to generate an explicit constraint for this anymore.
* You can assume that the order of elements is based on the numbers in its name (e.g. `Volcanologist1` is before `Volcanologist2`).
* The `solution` class contains mappings from every element to its corresponding fields. To find elements in a collection with specific characteristics, you must access the element via the properties of the `solution` class. Here are a few examples:

Puzzle condition: "Bob is the person who owns a dog"
Constraint:
```
bob = solution.name.bob
dog_owner = solution.pet.dog
assert bob == dog_owner
```

Puzzle condition: "The coffee drinker is taller than the tea drinker"
Constraint:
```
coffee_drinker = solution.drink.coffee
tea_drinker = solution.drink.tea
assert solution.height.coffee_drinker > solution.height.tea_drinker
```

* Use `immediatelyBefore` to express adjacency relations, e.g. `immediatelyBefore(a, b)` asserts that `a` is immediately before `b` (i.e. `Volcanologist1` is immediately before `Volcanologist2`). Here's an example:

Puzzle condition: "The green house is immediately to the right of the ivory house"
Constraint:
```
ivory_house = solution.color.ivory
green_house = solution.color.green
assert immediatelyBefore(ivory_house, green_house)
```

The validation function signature must look as follows:

```
def validate(solution: Solution) -> None
    # Your constraints belong here...
```

Now generate the conditions necessary to check that a solution to the puzzle is correct! Make sure that you consider every condition stated in the puzzle!"
"""

# Kicks off the data structure generation by the model.
_PUZZLE_PROMPT: str = """Here is the puzzle:
```
{}
```
"""

# Instructs the model to format the solver solution according to the requested format
_FORMAT_MESSAGE: str = """Your logic solver tool produced the following solution:
```
{solution}
```

Now convert it to the expected output format:
```
{output_format}
```"""

# Instructs the model on how to generate a solution data structure.
_DATA_STRUCTURE_MESSAGE: str = """You are an expert puzzle solving agent with access to a propositional logic solver tool that has a convenient interface optimised for you. Your boss has given you a logic puzzle that he thinks can be mapped to your logic solver tool. You must solve this puzzle in two steps:

1. Define the data type for a valid puzzle solution
2. Define the logical constraints for a valid puzzle solution


I will walk you through these steps one by one. Do not attempt to solve the puzzle or a following step before I tell you to do so. We will now begin with the first step: Define the data type for a valid puzzle solution.

Your solver tool allows you to specify the output solution type as Python classes, with a few additional features:

* Just like in SQL, each field can be marked as unique, meaning no two instances of the class can have the same value, e.g.: `id: Unique[int]`
* Each field can have a value constraint assigned to it, such that only these values are allowed, e.g.: `id: Domain[int, range(1, 11)]` allows id values between 1 (inclusive) and 11 (exclusive), or `name: Domain[str, \"John\", \"Jane\", \"Peter\"]` allows only the strings \"John\", \"Jane\", or \"Peter\". 
* You can define relationships between classes using the `Function` type, e.g.: `manager: Function[Domain[Employee, Employee]]` defines a mapping from each `Employee` to their `manager`, who is also an `Employee`. Note that functions are total, i.e. every instance of the source type must have a mapping to an instance of the target type.

Here is an example that uses these features in combination:
```
class Row:
    id: Unique[Domain[int, range(1, 4)]]

class Table:
    name: Function[Domain[tuple(Row, str), (Row1, \"Alice\"), (Row2, \"Bob\"), (Row3, \"Charlie\")]]]
    music: Function[Domain[tuple(Row, str), (Row1, \"Rock\"), (Row2, \"Jazz\"), (Row3, \"Classical\")]]]
```

Always constrain data types according to all the information you can identify in the puzzle text. This is critical for solving the puzzle.

In order to automatically validate the puzzle solution, your data structure will eventually need to be converted to JSON in the following format, so keep that in mind when deciding on your data structure:
```
{}
```

Now specify the type of a valid solution using this syntax."""

# Sent if the solver was unable to find a solution.
_UNSAT_MESSAGE: str = (
    "Your constraints are contradictory and thus the solver could not find a solution. Please review them and try to spot the error, we will go through the step of generating the `def validate(solution: Solution) -> None` function again."
)

class ForgeSearchEngineStrategy(EngineStrategy):
    """
    Implements the EngineStrategy interface for the Forge backend.
    """
    def __init__(
        self, logger_factory: Callable[[str], Logger], task: str, output_format: str
    ) -> None:
        """
        Args:
            logger_factory (Callable[[str], Logger]): Log configuration.
            task (str): Search-based problem to solve.
            output_format (str): Output format expected by the user.
        """
        self.__logger: Logger = logger_factory(__name__)
        self.__task: str = task
        self.__output_format: str = output_format
    
    @property
    def constraints_prompt(self) -> list[str]:
        return [_CONSTRAINTS_MESSAGE]
    
    @property
    def data_structure_prompt(self) -> str:
        """
        Prompt sent to the LLM instructing it to generate the data structure.
        """
        return _DATA_STRUCTURE_MESSAGE.format(self.__output_format)

    async def generate_solver_constraints(
        self, module: Module, metadata: Optional[MetadataWrapper]
    ) -> str:
        return LogicPyForgeHarnessGenerator.generate(metadata)

    def generate_solver_invocation_command(self, solver_input_file: str) -> list[str]:
        # TODO: Generate Forge solver command
        ...

    def get_format_prompt(self, solution: str) -> Optional[str]:
        """
        Prompt sent to the LLM instructing it to format the given
        solver-formatted solution to the actual output format expected by the
        user.

        Args:
            solution (str): Solution in solver format.
        Returns:
            Formatting prompt to send to LLM.
        """
        return _FORMAT_MESSAGE.format(solution=solution, output_format=self.__output_format)

    def parse_solver_output(
        self, exit_code: int, stdout: str, stderr: str
    ) -> Tuple[SolverOutcome, Optional[str]]:
        """
        Interprets the result of the constraint solver subprocess invocation.

        Args:
            exit_code (int): Constraint solver subprocess exit code.
            stdout (str): Standard output of constraint solver subprocess.
            stderr (str): Standard error output of constraint solver subprocess.
        Returns:
            A tuple where the first element indicates the outcome (i.e. whether
            we succeeded or should retry), and optionally the solution in solver
            format if the invocation was succesful.
        """
        # TODO: Parse Forge output
        ...
    
    @property
    def python_code_prefix(self) -> str:
        return ""

    @property
    def retry_prompt(self) -> str:
        return _UNSAT_MESSAGE

    @property
    def solver_input_file_suffix(self) -> str:
        return ".c"

    @property
    def system_prompt(self) -> str:
        """
        Initiates the first prompt sent to the LLM to describe the task.
        """
        return _PUZZLE_PROMPT.format(self.__task)
