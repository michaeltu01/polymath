# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""
OpenAI (and OpenAI-compatible) chat completion provider.

This implementation conforms to the ChatCompletion interface used across the
project and can be loaded dynamically via the plugin loader by setting the
following environment variables (typically in a .env file in the repo root):

  CHAT_COMPLETION_MODULE_PATH=/absolute/path/to/inference/openai_inference_provider.py
  CHAT_COMPLETION_CLASS_NAME=OpenAIChatCompletion

Required secrets / config (also via .env):
  OPENAI_API_KEY=<your key>
Optional:
  OPENAI_BASE_URL=<custom endpoint for OpenAI-compatible servers like vLLM>
  OPENAI_ORG=<your OpenAI org id>

Notes:
 - max_gen_tokens controls the maximum number of new tokens to generate. If 0,
   the provider default is used.
 - temperature is forwarded as-is.
 - The provider maps OpenAI finish_reason values to the internal FinishReason
   enum. In particular, "length" -> MAX_OUTPUT_TOKENS to enable automatic
   continuation in InferenceClient.
"""

from __future__ import annotations

import os
from types import TracebackType
from typing import Optional, Tuple

from inference.chat_completion import ChatCompletion, Message, Role
from inference.finish_reason import FinishReason

# Defer import to provide a helpful error if the package is missing.
try:
    from openai import AsyncOpenAI
    from openai import APIError, RateLimitError, APITimeoutError
    import httpx
except Exception as e:  # pragma: no cover - import guard
    AsyncOpenAI = None  # type: ignore[assignment]
    APIError = Exception  # type: ignore[assignment]
    RateLimitError = Exception  # type: ignore[assignment]
    APITimeoutError = Exception  # type: ignore[assignment]
    httpx = None  # type: ignore[assignment]


ROLE_MAP: dict[Role, str] = {
    Role.SYSTEM: "system",
    Role.USER: "user",
    Role.AI: "assistant",
}


class OpenAIChatCompletion(ChatCompletion):
    """ChatCompletion implementation backed by OpenAI's Chat Completions API.

    Compatible with OpenAI-compatible servers when OPENAI_BASE_URL is set
    (e.g., a local vLLM endpoint exposing the OpenAI schema).
    """

    def __init__(
        self,
        logger_factory,
        model_name: str,
        max_gen_tokens: int,
        max_tokens: int,
        temperature: float,
    ) -> None:
        if AsyncOpenAI is None:
            raise ImportError(
                "The 'openai' package is required. Install it with: pip install openai>=1.0"
            )
        if httpx is None:
            raise ImportError(
                "The 'httpx' package is required. Install it with: pip install httpx"
            )

        self.__logger = logger_factory(__name__)
        self.__model_name = model_name
        self.__max_gen_tokens = max_gen_tokens  # 0 -> use provider default
        self.__max_tokens = max_tokens  # Not directly used by OpenAI Chat API
        self.__temperature = 1

        api_key = os.getenv("OPENAI_API_KEY")
        if not api_key:
            raise ValueError(
                "OPENAI_API_KEY is not set. Add it to your .env or environment."
            )

        base_url = os.getenv("OPENAI_BASE_URL") or None
        organization = os.getenv("OPENAI_ORG") or None

        # Create custom httpx client without proxies to avoid compatibility issues
        http_client = httpx.AsyncClient(
            timeout=60.0,
            follow_redirects=True,
        )

        # Timeout is conservative; InferenceClient can handle retries.
        self.__client = AsyncOpenAI(
            api_key=api_key,
            base_url=base_url,
            organization=organization,
            http_client=http_client,
        )

    async def __aenter__(self) -> "OpenAIChatCompletion":
        return self

    async def __aexit__(
        self,
        exc_type: Optional[type[BaseException]],
        exc_value: Optional[BaseException],
        exc_tb: Optional[TracebackType],
    ) -> None:
        # Close the httpx client we created
        await self.__client.close()
        return None

    def __convert_messages(self, conversation: list[Message]) -> list[dict]:
        # Convert internal Message objects to OpenAI Chat API schema
        return [{"role": ROLE_MAP[m.role], "content": m.text} for m in conversation]

    async def create(
        self, conversation: list[Message]
    ) -> Tuple[FinishReason, Optional[str]]:
        try:
            messages = self.__convert_messages(conversation)
            kwargs: dict = {
                "model": self.__model_name,
                "messages": messages,
                "temperature": self.__temperature,
            }
            if self.__max_gen_tokens and self.__max_gen_tokens > 0:
                kwargs["max_tokens"] = self.__max_gen_tokens

            resp = await self.__client.chat.completions.create(**kwargs)

            if not resp.choices:
                # Defensive: treat as stopped with empty output
                return FinishReason.STOPPED, ""

            choice = resp.choices[0]
            text: str = choice.message.content or ""
            finish = (choice.finish_reason or "stop").lower()

            if finish == "length":
                return FinishReason.MAX_OUTPUT_TOKENS, text
            # content_filter/tool_calls/stop -> consider completion done
            return FinishReason.STOPPED, text

        except (RateLimitError, APITimeoutError) as e:
            self.__logger.warning(f"Retryable OpenAI error: {e}")
            return FinishReason.RETRYABLE_ERROR, None
        except APIError as e:
            status = getattr(e, "status_code", 0) or getattr(e, "status", 0)
            if isinstance(status, int) and status >= 500:
                self.__logger.warning(f"Retryable server error: {e}")
                return FinishReason.RETRYABLE_ERROR, None
            self.__logger.error(f"OpenAI API error: {e}")
            return FinishReason.STOPPED, ""
        except Exception as e:
            # Treat unexpected errors as retryable to allow the client to reattempt.
            self.__logger.warning(f"Transient error: {e}")
            return FinishReason.RETRYABLE_ERROR, None
