# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from abc import ABC, abstractmethod
from typing import Any


class ScorerVCSampleParser(ABC):
    """
    Helper to parse a regular sample into a scorer VC semantic sample. Usually
    we generate scorer VCs at the same time as we generate the natural language
    sample. Implementations of this interface are used when we need to generate
    VCs for an existing dataset after the fact.
    """

    @abstractmethod
    def parse(self, line: str) -> tuple[str, str, str, dict[str, Any]]:
        """
        Takes a sample JSON object (usually from a `.jsonl` file) and converts
        it to all properties necessary for constructing a scorer VC sample.

        Args:
            line (str): JSON object fron `.jsonl` dataset line.
        Returns:
            A tuple of the puzzle task to send to the model as a message, the
            Logic.py data structure and Logic.py constraint describing the
            correct solution, and the JSON solution matching the Logic.py data
            structure.
        """
        ...
