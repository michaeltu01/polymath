# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

import asyncio
from logging import Logger
from typing import Callable, Optional

from inference.chat_completion import ChatCompletion
from inference.finish_reason import FinishReason

# AI assistant role name
AI: str = "ai"
# User role name
USER: str = "user"
# System role name
SYSTEM: str = "system"

# Number of times we ask the model to continue or retry a request If the model hits a token limit or we get a failure HTTP status code.
RETRY_LIMIT: int = 5

# Message we send if we hit a token limit.
CONTINUATION_MESSAGE: str = (
    "It seems you encountered a token limit during your last response, most likely when generating the constraint function. I removed the last, incomplete line. Start with a newline and a single indentation, and continue exactly where you left off. Do not repeat anything that you already sent in the previous message and do not add additional output. I need to be able to concatenate your next message to the previous one. Make sure you still wrap all code in ``` markers."
)


class InferenceClient:
    """
    Inference client wrapping chat completions API. Implements conversation
    memory and automated retries on token limits and other retryable errors.
    """

    def __init__(
        self,
        logger_factory: Callable[[str], Logger],
        chat_completion: ChatCompletion,
    ) -> None:
        self.conversation: list[dict[str, str]] = []
        self.__logger: Logger = logger_factory(__name__)
        self.__chat_completion = chat_completion

    async def send(self) -> Optional[str]:
        """
        Sends the current full conversation history to the chat completions API.
        """

        attempt: int = 0
        multi_message_ai_response: str = ""
        while True:
            finish_reason, ai_response = await self.__chat_completion.create(
                self.conversation
            )
            if finish_reason == FinishReason.RETRYABLE_ERROR:
                attempt += 1
                if attempt >= RETRY_LIMIT:
                    self.__logger.error("Chat completion API errors occurred.")
                    return None

                await asyncio.sleep(30)
                continue

            ai_response = ai_response or ""
            if finish_reason == FinishReason.MAX_OUTPUT_TOKENS:
                attempt += 1
                if attempt >= RETRY_LIMIT:
                    self.__logger.error(
                        "Token limit occurred and exceeded retry limit."
                    )
                    break

                self.__logger.warning(
                    "Encountered token limit, asking model to continue..."
                )

                last_newline_index = ai_response.rfind("\n")
                if last_newline_index != -1:
                    ai_response = ai_response[: last_newline_index + 1]

                self.add_message(ai_response, AI)
                multi_message_ai_response += ai_response
                self.add_message(CONTINUATION_MESSAGE, USER)
                continue

            self.add_message(ai_response, AI)
            multi_message_ai_response += ai_response
            break

        return multi_message_ai_response

    def add_message(self, text: str, role: str) -> None:
        """
        Adds the given message to the conversation history.
        """
        self.conversation.append({"text": text, "role": role})
