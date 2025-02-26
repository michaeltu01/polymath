# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from asyncio import gather, Semaphore
from typing import Callable, Coroutine


class AsyncPool:
    """
    Helper to invoke `async` tasks concurrently, with a configurable maximum
    concurrency level.
    """

    def __init__(self, max_concurrency: int):
        self.__semaphore = Semaphore(max_concurrency)
        self.__tasks: list[Coroutine] = []

    def submit(self, task: Callable[[], Coroutine]):
        """
        Accepts a factory for an async task which is executed in a pool with
        configurd maximum concurrency.
        """
        self.__tasks.append(self.__run_with_semaphore(task))

    async def gather(self):
        """
        Wait until all tasks scheduled via `submit` are completed.
        """
        await gather(*self.__tasks)

    async def __run_with_semaphore(self, task: Callable[[], Coroutine]):
        """
        Invokes and awaits `task` while acquiring `self.__semaphore`. This
        ensure that only the maximum allowed number of tasks run concurrently.
        """
        async with self.__semaphore:
            await task()
