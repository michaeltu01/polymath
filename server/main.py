# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from uvicorn import run
from openapi_server.main import app
from server.agent_chat_api import LogicAgentChatApi


def main() -> None:
    """
    Starts a uvicorn test server of an OpenAI compatible REST API, registering a
    chat completion endpoint handler which delegates to our logic agent.

    TODO: Starting this server should be part of a tau-bench benchmark runner,
    and this test module should be removed.
    """
    LogicAgentChatApi()
    run(app)


if __name__ == "__main__":
    main()
