# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from openapi_server.apis.chat_api_base import BaseChatApi
from openapi_server.models.create_chat_completion_request import CreateChatCompletionRequest
from openapi_server.models.create_chat_completion_response import CreateChatCompletionResponse

class LogicAgentChatApi(BaseChatApi):
    """
    Implements OpenAI's BaseChatApi by invoking the logic agent with the given
    dialog. We assume the dialog contains a compatible benchmark problem. This
    is a convenient way to evaluate our logic agent against existing benchmarks
    which are likely to suppor the OpenAI API.
    """

    async def create_chat_completion(
        self,
        create_chat_completion_request: CreateChatCompletionRequest,
    ) -> CreateChatCompletionResponse:
        return CreateChatCompletionResponse(
            id="123",
            choices=[],
            created=0,
            model="",
            object="chat.completion"
        )
