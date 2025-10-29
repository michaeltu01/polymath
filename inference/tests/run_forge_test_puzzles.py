import asyncio
import os
from importlib import import_module
from logging import getLogger
from io import StringIO
from pathlib import Path

from dotenv import load_dotenv

from agent.logic.forge.forge_agent import ForgeAgent
from agent.logic.forge.forge_search_engine_strategy import ForgeSearchEngineStrategy
from agent.logic.zebra_benchmark import ZebraBenchmark
from inference.chat_completion import Role
from inference.chat_completion_factory import create_chat_completion
from judge.result_trace import ResultTrace
from logger.logger_factory import LoggerFactory


# Dictionary mapping puzzle files to their configuration
# Key: (num_houses, header_list)
# Value: puzzle file name
PUZZLE_CONFIGS = {
    # TODO: Fill in manually
    # Example: (4, ["Person", "Name", "Occupation", "BookGenre", "Phone"]): "puzzle1.txt",
    "puzzle1.txt": (4, ["Person", "Name", "Occupation", "BookGenre", "Phone"]),
    "puzzle2.txt": (2, ["Person", "Name", "Style", "Phone"]), 
    "puzzle3.txt": (5, ["Person", "Name", "Phone"]),
}


def build_solution_placeholder(num_houses: int, header: list[str]) -> dict:
    return {
        "header": header,
        "rows": [[] for _ in range(num_houses)],
    }


async def run_puzzle(puzzle_config: tuple[tuple[int, list[str]], str], model_name: str) -> tuple[str, bool, str]:
    """
    Run a single puzzle and return (puzzle_name, success, solution_or_error)
    puzzle_config: (puzzle_filename, ((num_houses, header)))
    """
    puzzle_filename, ((num_houses, header)) = puzzle_config
    puzzle_name = Path(puzzle_filename).stem
    
    try:
        # Read puzzle content
        test_puzzles_dir = "/Users/mstu/courses/cs1970/polymath/test_puzzles"
        puzzle_path = os.path.join(test_puzzles_dir, puzzle_filename)
        
        with open(puzzle_path, 'r', encoding='utf-8') as f:
            puzzle_text = f.read()
        
        # Use the provided configuration
        solution_placeholder = build_solution_placeholder(num_houses, header)
        output_format = ZebraBenchmark.get_format(solution_placeholder)
        
        result_trace = ResultTrace(f"forge-test-{puzzle_name}")
        
        log_buffer = StringIO()
        with LoggerFactory(log_buffer) as logger_factory:
            async with create_chat_completion(getLogger, model_name) as chat:
                engine = ForgeSearchEngineStrategy(logger_factory, puzzle_text, output_format)
                agent = ForgeAgent(logger_factory, chat, engine, result_trace)
                
                await agent.solve()
        
        solution = result_trace.solution
        if solution and solution.strip() and solution.strip() != "(no solution)":
            return puzzle_name, True, solution
        else:
            return puzzle_name, False, "No solution found"
    
    except Exception as e:
        return puzzle_name, False, f"Error: {str(e)}"


async def main() -> None:
    load_dotenv()
    
    # Get model name from environment or use default
    model_name = os.getenv("SMOKE_MODEL_NAME", "gpt-4o-mini")
    
    # Check if puzzle configurations are filled in
    if any(config == () for config in PUZZLE_CONFIGS.keys()):
        print("❌ ERROR: PUZZLE_CONFIGS dictionary contains empty configurations.")
        print("Please fill in the (num_houses, header) tuples for each puzzle file.")
        print("\nExample:")
        print('PUZZLE_CONFIGS = {')
        print('    (4, ["Person", "Name", "Occupation", "BookGenre", "Phone"]): "puzzle1.txt",')
        print('    (2, ["Person", "Name", "HouseStyle", "Phone"]): "puzzle2.txt",')
        print('    (5, ["Person", "Name", "Phone"]): "puzzle3.txt",')
        print('}')
        return
    
    print(f"Found {len(PUZZLE_CONFIGS)} puzzle configurations:")
    for filename, (num_houses, header) in PUZZLE_CONFIGS.items():
        print(f"  - {filename}: {num_houses} houses, {len(header)} attributes")
    print(f"\nUsing model: {model_name}")
    print("=" * 60)
    
    results = []
    
    # Run each puzzle
    for puzzle_filename, config in PUZZLE_CONFIGS.items():
        print(f"\n🔍 Running {puzzle_filename}...")
        
        puzzle_config = (puzzle_filename, config)
        puzzle_name, success, result = await run_puzzle(puzzle_config, model_name)
        results.append((puzzle_name, success, result))
        
        if success:
            print(f"✅ {puzzle_name}: SUCCESS")
            print(f"Solution: {result[:100]}{'...' if len(result) > 100 else ''}")
        else:
            print(f"❌ {puzzle_name}: FAILED")
            print(f"Error: {result}")
    
    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    
    successful = sum(1 for _, success, _ in results if success)
    total = len(results)
    
    print(f"Results: {successful}/{total} puzzles solved successfully")
    print()
    
    for puzzle_name, success, result in results:
        status = "✅ PASS" if success else "❌ FAIL"
        print(f"{status}: {puzzle_name}")
        if not success:
            print(f"       {result}")
    
    # Write detailed log
    log_path = os.getenv("FORGE_TEST_LOG_PATH", "forge_test_puzzles.log")
    with open(log_path, "w", encoding="utf-8") as f:
        f.write(f"Forge Test Puzzles Report\n")
        f.write(f"Model: {model_name}\n")
        f.write(f"Results: {successful}/{total} successful\n\n")
        
        for puzzle_name, success, result in results:
            f.write(f"=== {puzzle_name} ===\n")
            f.write(f"Status: {'SUCCESS' if success else 'FAILED'}\n")
            f.write(f"Result: {result}\n\n")
    
    print(f"\nDetailed log written to {os.path.abspath(log_path)}")


if __name__ == "__main__":
    asyncio.run(main())