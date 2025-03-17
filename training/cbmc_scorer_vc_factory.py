# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from logging import Logger
from os import remove
from typing import Callable, Optional

from aiofiles import open
from aiofiles.tempfile import NamedTemporaryFile

from concurrency.subprocess import Subprocess


class CBMCScorerVerificationConstraintsFactory:
    """
    Helper class to create RL scorer VCs for a CBMC back-end.
    """

    def __init__(self, logger_factory: Callable[[str], Logger]) -> None:
        self.__logger: Logger = logger_factory(__name__)

    async def convert(self, cbmc_c_solver_constraints: str) -> Optional[str]:
        """
        Converts the given CBMC solution synthesis C code into an instrumented
        GOTO binary that scores a solution.

        Args:
            cbmc_c_solver_constraints (str): C code used to synthesise correct
            solution.
        Returns:
            Binary file content of a GOTO binary that scores a solution. Binary
            file content is encoded using `bytes.hex()`.
        """
        goto_file_name: str
        async with NamedTemporaryFile(
            mode="w", suffix=".c", delete_on_close=False
        ) as c_file:
            await c_file.write(cbmc_c_solver_constraints)
            await c_file.close()

            c_file_name: str = str(c_file.name)
            goto_file_name = c_file_name.replace(".c", ".gb")
            exit_code, stdout, stderr = await Subprocess.run(
                "goto-cc", "-D__CPROVER", c_file_name, "-o", goto_file_name
            )
            if exit_code != 0:
                self.__logger.error(
                    f"""CBMC compilation error.
C Code:
{cbmc_c_solver_constraints}

Output:
{stdout}
{stderr}
"""
                )
                return None

        scorer_vc_file_name: str = goto_file_name.replace(".gb", "-mod.gb")
        try:
            exit_code, stdout, stderr = await Subprocess.run(
                "goto-instrument",
                "--polymath-convert",
                goto_file_name,
                scorer_vc_file_name,
            )
        finally:
            remove(goto_file_name)

        if exit_code != 0:
            self.__logger.error(
                f"""CBMC instrumentation error.
C Code:
{cbmc_c_solver_constraints}

Output:
{stdout}
{stderr}
"""
            )
            return None

        scorer_vc: bytes
        async with open(scorer_vc_file_name, "rb") as file:
            scorer_vc = await file.read()
        return scorer_vc.hex()
