# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from inference.chat_completion import ChatCompletion
from inference.dummy_chat_completion import DummyChatCompletion
from logger.logger_factory import LoggerFactory
from plugin.plugin_loader import PluginLoader


# Default max token configuration to use for LLM inference.
DEFAULT_MAX_TOKENS: int = 131072
# DEFAULT_MAX_TOKENS: int = 4096

# Default temperature to use for LLM inference.
DEFAULT_TEMPERATURE: float = 0.5


def create_chat_completion(
    logger_factory: LoggerFactory, model_name: str
) -> ChatCompletion:
    """
    Default factory for chat completion API. Modifying this method allows to
    activate a custom chat completion API (e.g. OpenAI) across benchmarks and
    end-to-end tests.

    Additionally, a chat completion implementation from an external module can
    be configured dynamically using the environment variables
    `CHAT_COMPLETION_MODULE_PATH` and `CHAT_COMPLETION_CLASS_NAME`. They must
    provide the same constructor as DummyChatCompletion and implement the
    ChatCompletion interface.

    Args:
        logger_factory (Callable[[str], Logger]): Logging configuration to
        use.
        model_name (str): Name of model to use in LLM chat completion client.
    Returns: Chat completion API to use for inference.
    """
    plugin: PluginLoader[ChatCompletion] = PluginLoader("chat_completion")
    if plugin.is_configured:
        return plugin.factory(
            logger_factory, model_name, DEFAULT_MAX_TOKENS, DEFAULT_TEMPERATURE
        )

    return DummyChatCompletion(
        logger_factory, model_name, DEFAULT_MAX_TOKENS, DEFAULT_TEMPERATURE
    )
