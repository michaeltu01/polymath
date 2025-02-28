# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from dataclasses import dataclass
from importlib.abc import Loader
from importlib.machinery import ModuleSpec
from importlib.util import module_from_spec, spec_from_file_location
from os import getenv
from types import ModuleType
from typing import Optional, Type

from inference.chat_completion import ChatCompletion
from inference.dummy_chat_completion import DummyChatCompletion
from logger.logger_factory import LoggerFactory


@dataclass
class ChatCompletionPlugin:
    """
    Used to load chat completion implementations dynamically based on
    configuration environment variables.
    """

    # Path to .py file containing chat completion class.
    module_path: str

    # Name of chat completion class in module_name.
    class_name: str


def _get_chat_completion_plugin_from_env() -> Optional[ChatCompletionPlugin]:
    """
    Reads a ChatCompletionPlugin from matching environment variables, if
    present.

    Returns: Chat completion plugin information, if the necessary environment
    variables were set, None otherwise.
    """
    module_path: Optional[str] = getenv("CHAT_COMPLETION_MODULE_PATH")
    if module_path is None:
        return None
    class_name: Optional[str] = getenv("CHAT_COMPLETION_CLASS_NAME")
    if class_name is None:
        return None

    return ChatCompletionPlugin(module_path, class_name)


def create_chat_completion(
    logger_factory: LoggerFactory, model_name: str
) -> ChatCompletion:
    """
    Default factory for chat completion API. Modifying this method allows to
    activate a custom chat completion API (e.g. OpenAI) across benchmarks and
    end-to-end tests.

    Additionally, a chat completion implementation from an external module can
    be configured dynamically using the environment variables
    `CHAT_COMPLETION_MODULE_PATH` and `CHAT_COMPLETION_CLASS_NAME`.

    Args:
        logger_factory (Callable[[str], Logger]): Logging configuration to
        use.
        model_name (str): Name of model to use in LLM chat completion client.
    Returns: Tuple of finish reason and LLM response text.
    """
    plugin: Optional[ChatCompletionPlugin] = _get_chat_completion_plugin_from_env()
    if plugin is not None:
        spec: Optional[ModuleSpec] = spec_from_file_location(
            "inference.dynamic_chat_completion", plugin.module_path
        )
        if spec:
            plugin_module: ModuleType = module_from_spec(spec)
            loader: Optional[Loader] = spec.loader
            if loader:
                loader.exec_module(plugin_module)

            class_name: str = plugin.class_name
            plugin_class: Type[ChatCompletion] = getattr(plugin_module, class_name)
            return plugin_class(logger_factory, model_name, 131072, 0.5)

    return DummyChatCompletion(logger_factory, model_name, 131072, 0.5)
