# Simple smoke test for the configured ChatCompletion provider.

import asyncio
import os
from logging import getLogger

from dotenv import load_dotenv

from inference.chat_completion import Role
from inference.chat_completion_factory import create_chat_completion
from inference.client import InferenceClient


async def main() -> None:
    load_dotenv()
    model = os.getenv("SMOKE_MODEL_NAME", "gpt-4o-mini")

    async with create_chat_completion(getLogger, model) as chat:
        client = InferenceClient(getLogger, chat)
        client.add_message("You are a friendly, concise assistant.", Role.SYSTEM)
        client.add_message("Reply with just the word: Hello", Role.USER)
        out = await client.send()
        print("[SMOKE OUTPUT]", out)


if __name__ == "__main__":
    asyncio.run(main())
