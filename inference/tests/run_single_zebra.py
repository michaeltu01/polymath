import asyncio
import os
from importlib import import_module
from logging import getLogger
from io import StringIO

from dotenv import load_dotenv

from agent.logic.agent import LogicAgent
from agent.logic.cbmc_search_engine_strategy import CBMCSearchEngineStrategy
from agent.logic.zebra_benchmark import ZebraBenchmark
from inference.chat_completion import Role
from inference.chat_completion_factory import create_chat_completion
from judge.result_trace import ResultTrace
from logger.logger_factory import LoggerFactory


# Paste or import your puzzle text here. For convenience, we allow providing
# a path via the RUN_SINGLE_ZEBRA_FILE environment variable to read the puzzle
# from a .txt file. If not set, we fall back to the inline constant.
INLINE_PUZZLE = """
Zebra Puzzle

    Shape:
        4 Volcanologists
        Laptop: green, pink, purple, yellow
        Name: emily, kimberly, lauren, samantha
        Volcano: lavadome, scoriacone, submarine, supervolcano
        Activity: fluctuating, increasing, stable, veryhigh

    Clues:
    - The volcanologist monitoring a volcano with a Very high activity level is in the second position.
    - The scientist studying the Supervolcano is in the third position.
    - The scientist who is monitoring the Lava dome volcano is immediately after the scientist studying the Supervolcano.
    - The volcanologist who is monitoring the Scoria cone volcano is observing a Fluctuating activity level.
    - Lauren is in the second position.
    - The scientist observing a volcano with a Stable activity level is next to Samantha.
    - The volcanologist studying the Submarine volcano is immediately after the scientist using the Yellow laptop.
    - The volcanologist monitoring a volcano with an Increasing activity level is immediately after the scientist using the Pink laptop.
    - Emily is immediately after the volcanologist who is using the Purple laptop.
    - Lauren is immediately before Emily.
"""


def build_solution_placeholder(num_houses: int, header: list[str]) -> dict:
    return {
        "header": header,
        "rows": [[] for _ in range(num_houses)],
    }


async def main() -> None:
    load_dotenv()

    # If you want to override the model, set SMOKE_MODEL_NAME in .env
    model_name = os.getenv("SMOKE_MODEL_NAME", "gpt-4o-mini")

    # Puzzle input:
    puzzle = INLINE_PUZZLE.strip()

    # Configure the expected output format using the helper from ZebraBenchmark
    # House + 4 attributes => header length 5; number of houses inferred from puzzle
    # Here we set 4 houses for this specific puzzle.
    num_volcanologists = 4
    header = [
        "Volcanologist",
        "Laptop",
        "Name",
        "Volcano",
        "Activity",
    ]
    solution_placeholder = build_solution_placeholder(num_volcanologists, header)
    output_format = ZebraBenchmark.get_format(solution_placeholder)

    print("Output format:", output_format)

    result_trace = ResultTrace("single-zebra")

    log_buffer = StringIO()
    with LoggerFactory(log_buffer) as logger_factory:
        async with create_chat_completion(getLogger, model_name) as chat:
            # Use the CBMC-backed search engine to solve the puzzle
            engine = CBMCSearchEngineStrategy(logger_factory, puzzle, output_format)
            agent = LogicAgent(logger_factory, chat, engine, result_trace)

            # Provide a minimal system prompt for consistency
            # agent.client.add_message(
            #     "You are a careful reasoning assistant that outputs only the requested JSON.",
            #     Role.SYSTEM,
            # )

            await agent.solve()

    print("\n=== Solution (ZeroEval format) ===\n")
    print(result_trace.solution or "(no solution)")

    print("\n=== Conversation trace ===\n")
    for m in result_trace.messages:
        role = getattr(m, "role", Role.USER)
        text = getattr(m, "text", "")
        print(role.name, ":", text.strip(), "\n")
    
    # Persist logs to a log file
    log_path = os.getenv("ZEBRA_LOG_PATH", "single_zebra_run.log")
    with open(log_path, "a", encoding="utf-8") as f:
        f.write(log_buffer.getvalue())
    print(f"\nLogs written to {os.path.abspath(log_path)}")


if __name__ == "__main__":
    asyncio.run(main())
