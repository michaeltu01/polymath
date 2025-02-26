# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from logging import getLogger
from unittest import IsolatedAsyncioTestCase

from dotenv import load_dotenv
from inference.client import InferenceClient, SYSTEM, USER
from inference.tests.mock_chat_completion import MockChatCompletion


load_dotenv()


class TestInferenceClient(IsolatedAsyncioTestCase):

    async def test_single(self) -> None:
        async with MockChatCompletion(["Hello, I am an AI."]) as chat_completion:
            client = InferenceClient(getLogger, chat_completion)
            client.add_message("Say hello, please!", USER)
            self.assertEqual("Hello, I am an AI.", await client.send())
            self.assertEqual(
                [
                    {"text": "Say hello, please!", "role": "user"},
                    {"text": "Hello, I am an AI.", "role": "ai"},
                ],
                client.conversation,
            )

    async def test_conversation(self) -> None:
        async with MockChatCompletion(["Hi Mate, I am an AI."]) as chat_completion:
            client = InferenceClient(getLogger, chat_completion)
            client.add_message("Address the user as `mate`.", SYSTEM)
            client.add_message("Hi! How are you?", USER)
            self.assertEqual("Hi Mate, I am an AI.", await client.send())
            self.assertEqual(
                [
                    {"text": "Address the user as `mate`.", "role": "system"},
                    {"text": "Hi! How are you?", "role": "user"},
                    {"text": "Hi Mate, I am an AI.", "role": "ai"},
                ],
                client.conversation,
            )
