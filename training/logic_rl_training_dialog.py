# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.


from json import dumps

from inference.chat_completion import Message, Role
from libcst import Module, parse_module
from training.training_data_structure_converter import (
    PythonDataStructureToJsonSchemaConverter,
)


# System prompt instructing the model to generate a JSON output that we can
# score using scorer VCs.
_LOGIC_RL_TRAINING_DIALOG_SYSTEM_PROMPT_TEMPLATE: str = """You are an expert logician and are tasked to answer a reasoning question. You should give your answer in the form of a JSON object, following this JSON schema:

```
{}
```

Please split your answer into a `# Thinking` section, where you can put your reasoning, comments, or any explanation of the solution you would like to add, and a `# Solution` section, containing only the raw JSON without highlighting or other markers. For example:
```
# Thinking
Put any thoughts, comments or descriptions here...

# Solution
{{
  "entities": [
    ...
  ]
}}
```

Here is the user's question:
"""


class LogicRlTrainingDialog:
    """
    Helper to create dialog data used for constraint solver enabled training.
    """

    @staticmethod
    def create(user_question: str, python_data_structure: str) -> list[Message]:
        """
        Creates a chat completions dialog suitable for RL training.

        Args:
            user_question (str): Benchmark question or task.
            python_data_structure (str): Python data structure that can represent a
            solution to the user question.
        Returns:
            System prompt and user message to send to model during RL training.
        """
        module: Module = parse_module(python_data_structure)
        visitor = PythonDataStructureToJsonSchemaConverter()
        module.visit(visitor)
        json_schema: str = dumps(visitor.json_schema, indent=4)

        return [
            Message(
                Role.SYSTEM,
                _LOGIC_RL_TRAINING_DIALOG_SYSTEM_PROMPT_TEMPLATE.format(json_schema),
            ),
            Message(Role.USER, user_question),
        ]
