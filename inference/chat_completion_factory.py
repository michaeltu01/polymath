# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from inference.chat_completion import ChatCompletion
from inference.dummy_chat_completion import DummyChatCompletion
from logger.logger_factory import LoggerFactory


def create_chat_completion(
    logger_factory: LoggerFactory, model_name: str
) -> ChatCompletion:
    """
    Default factory for chat completion API. Modifying this method allows to
    activate a custom chat completion API (e.g. OpenAI) across benchmarks and
    end-to-end tests.

    Args:
        logger_factory (Callable[[str], Logger]): Logging configuration to
        use.
        model_name (str): Name of model to use in LLM chat completion client.
    Returns: Tuple of finish reason and LLM response text.
    """
    # TODO: Select your chat completion implementation here
    return DummyChatCompletion(logger_factory, model_name, 131072, 0.5)
