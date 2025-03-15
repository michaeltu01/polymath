# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from abc import ABC, abstractmethod
from typing import Any


class SampleOutputConverter(ABC):
    """
    Classes implementing this interface write sample data for training to an
    output stream. Usually, this is done in the form of a `.jsonl` output file,
    where each sample is written as a JSON line.
    """

    @abstractmethod
    def convert(self, dialog: list[dict[str, str]], metadata: dict[str, Any]) -> Any:
        """
        Takes the given user-agent dialog as well as any additional metadata
        necessary for training and writes them as a sample to output.

        Args:
            dialog (list[dict[str, str]]): Dialog to include in sample.
            TODO: Refactor here and in InferenceClient to Message class instead
            of dictionary.
            metadata (dict[str, Any]): Additional, converter-specific metadata
            for sample. Contains e.g. verification constraints.
        Returns:
            JSON object that can be e.g. written to a `jsonl` file.
        """
        ...
