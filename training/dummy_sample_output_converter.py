# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from typing import Any

from inference.chat_completion import Message
from training.sample_output_converter import SampleOutputConverter


class DummySampleOutputConverter(SampleOutputConverter):
    """
    Dummy implementation of SampleOutputConverter. You should create your own
    implementation for your training data format.
    """

    def convert(self, dialog: list[Message], metadata: dict[str, Any]) -> Any:
        return {}
