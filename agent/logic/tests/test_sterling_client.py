from agent.logic.forge.forge_search_engine_strategy import ForgeSearchEngineStrategy
from concurrency.subprocess import Subprocess
import asyncio
import os
import json
from unittest import TestCase

class TestSterlingClientConnection(TestCase):
    def __init__(self, methodName="runTest"):
        super().__init__(methodName)
        self.maxDiff = None
        self.default_port = 4000

    # FIXME: This function duplicates code in forge_agent.py. Change this test to use helper function from forge_agent.py.
    async def util_communicate_to_sterling_client(
        self,
        solver_input_file: str,
        engine_strategy: ForgeSearchEngineStrategy
    ) -> tuple[str | None, int | None]:
        solver_exit_code: int | None = None
        solver_output: str | None = None

        try:
            forge_process = await Subprocess.run_in_background(
                *engine_strategy.generate_solver_invocation_command(
                    solver_input_file
                ),
            )

            try: 
                # Wait a moment for the Sterling WebSocket server to start up
                # Poll the server until it's ready
                print("Waiting for Sterling server to start...")
                max_wait_time = 30 # seconds
                poll_interval = 0.5 # Check every 0.5 seconds
                elapsed_time = 0.0

                while elapsed_time < max_wait_time:
                    # Check if the Forge process exited early
                    if forge_process.returncode is not None:
                        # Server exited, read the error output
                        stdout_data = await forge_process.stdout.read()
                        stderr_data = await forge_process.stderr.read()
                        solver_output = f"Forge server exited early with code {forge_process.returncode}\nstdout:\n{stdout_data.decode()}\nstderr:\n{stderr_data.decode()}"
                        solver_exit_code = forge_process.returncode
                        return solver_output, solver_exit_code
                    
                    # Check if port 4000 is listening
                    if await self._is_port_listening(self.default_port):
                        print(f"Sterling server is up after {elapsed_time:.1f}!")
                        break

                    await asyncio.sleep(poll_interval)
                    elapsed_time += poll_interval
                else:
                    # Timeout waiting for server to start
                    solver_output = "Timeout waiting for Sterling server to start"
                    solver_exit_code = 1
                    return solver_output, solver_exit_code

                # Connect with WebSocket client to get instances
                print("Connecting to Sterling client...")
                from mock_sterling.test_mock_sterling import MockSterlingClient
                client = MockSterlingClient(port=self.default_port)
                alloy_instance = await client.run_sterling_client()

                if alloy_instance:
                    solver_output = json.dumps(alloy_instance, indent=2)
                    solver_exit_code = 0
                else:
                    solver_output = "Failed to get Alloy instance from Sterling server"
                    solver_exit_code = 1
            
            finally:
                # Clean up: terminate the Forge server if still running
                if forge_process.returncode is None:
                    forge_process.terminate()
                try:
                    await asyncio.wait_for(forge_process.wait(), timeout=5)
                except asyncio.TimeoutError:
                    forge_process.kill()
                    await forge_process.wait()
            
                # Clean up the temp file
                # os.unlink(solver_input_file)
            
        except TimeoutError:
            # Clean up the temp file
            # os.unlink(solver_input_file)
            return None, 1

        return solver_output, solver_exit_code
    
    async def _is_port_listening(self, port: int) -> bool:
        """
        Check if a localhost port is listening for connections.
        """
        try:
            reader, writer = await asyncio.wait_for(
                asyncio.open_connection('127.0.0.1', port), # NOTE: using localhost
                timeout=0.5
            )
            writer.close()
            await writer.wait_closed()
            return True
        except (ConnectionRefusedError, asyncio.TimeoutError, OSError):
            return False

    def test_sterling_client_connection(self) -> None:
        # Mock a ForgeEngineSearchStrategy object
        from unittest.mock import Mock
        from logging import getLogger
        
        engine_strategy = Mock()
        engine_strategy.generate_solver_invocation_command.return_value = [
            "racket", 
            "", # File name will be inserted here dynamically
            "-O", "run_sterling", "serve", 
            "-O", "sterling_port", "4000"
        ]

        # Build the file name
        file_name: str = "/Users/mstu/courses/cs1970/polymath/forge-test.frg"
        
        # Update the mock to use the actual file name
        engine_strategy.generate_solver_invocation_command.return_value[1] = file_name

        # Run `util_communicate_to_sterling_client` on the file name
        solver_output, solver_exit_code = asyncio.run(
            self.util_communicate_to_sterling_client(file_name, engine_strategy)
        )

        # Print the exit code and output
        print(f"\n{'='*60}")
        print(f"Exit Code: {solver_exit_code}")
        print(f"{'='*60}")
        print(f"Output:\n{solver_output}")
        print(f"{'='*60}\n")
        
        # Assertions
        self.assertIsNotNone(solver_output, "Solver output should not be None")
        self.assertEqual(solver_exit_code, 0, "Solver should exit successfully")
