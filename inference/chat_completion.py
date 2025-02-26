# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from abc import ABC, abstractmethod
from types import TracebackType
from typing import Optional, Tuple

from inference.finish_reason import FinishReason


class ChatCompletion(ABC):

    @abstractmethod
    async def __aenter__(self) -> "ChatCompletion": ...

    async def __aexit__(
        self,
        exc_type: Optional[type[BaseException]],
        exc_value: Optional[BaseException],
        exc_tb: Optional[TracebackType],
    ) -> None: ...

    @abstractmethod
    async def create(
        self, conversation: list[dict[str, str]]
    ) -> Tuple[FinishReason, Optional[str]]:
        """
        Sends the given conversation to chat completions inference back-end.
        This is just a dummy implementation. You should create your own
        implementation with access to your specific LLM inference back-end. We
        will provide some default implementations for this class in the future,
        e.g. for the OpenAI API.

        Returns: Tuple of finish reason and LLM response text.
        """
        ...
