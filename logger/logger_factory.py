# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from io import StringIO
from logging import getLogger, Logger, PlaceHolder, root, StreamHandler
from types import TracebackType
from typing import Optional


class LoggerFactory:
    """
    Factory for per-benchmark isolated loggers. Created loggers output to
    stderr and a configured `StringIO`. Will destroy all loggers it created
    when disposed.
    """

    def __init__(self, output: StringIO, enable_stderr_log: bool = True) -> None:
        self.__output: StringIO = output
        self.__id: int = id(self)
        self.__created_loggers: set[str] = set()
        self.__enable_stderr_log: bool = enable_stderr_log

    def __enter__(self) -> "LoggerFactory":
        return self

    def __exit__(
        self,
        exc_type: Optional[type[BaseException]],
        exc_value: Optional[BaseException],
        exc_tb: Optional[TracebackType],
    ) -> None:
        for name in self.__created_loggers:
            logger: Logger | PlaceHolder = root.manager.loggerDict.pop(name)
            if isinstance(logger, Logger):
                logger.handlers.clear()

    def __call__(self, name: str) -> Logger:
        qualified_name: str = f"{name}-{self.__id}"
        logger = getLogger(qualified_name)
        self.__created_loggers.add(qualified_name)
        if not logger.hasHandlers():
            if self.__enable_stderr_log:
                logger.addHandler(StreamHandler())
            logger.addHandler(StreamHandler(self.__output))
        return logger
