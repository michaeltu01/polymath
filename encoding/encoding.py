# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.


class Encoding:
    """
    Helper for common string conversion operations.
    """

    @staticmethod
    def decode_process_output(output: bytes) -> str:
        """
        Decodes subprocess stdout and stderr outputs.

        Args:
            output (bytes): Raw stdout or stderr from a completed subprocess.
        Returns:
            UTF-8 decoded string of output.
        """
        return output.decode("utf-8")
