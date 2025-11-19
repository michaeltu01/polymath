"""
Test script for running the mock Sterling WebSocket client.

This script demonstrates how to:
1. Run the TypeScript WebSocket client via start.sh
2. Connect to an already-running Forge/Sterling server on port 4000
3. Capture JSON output conforming to the alloyDatumSchema

This pattern can be refactored into forge_agent.py's __generate_and_verify_constraints
to integrate Forge solver output with the agent.

ASSUMPTION: The Forge/Sterling server is already running on the specified port
with the solver constraints file loaded.
"""

import asyncio
import json
import os
import sys
from typing import Optional, Dict, Any
from pathlib import Path

# Add parent directory to path to enable imports
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from concurrency.subprocess import Subprocess


class MockSterlingClient:
    """
    Client for running the mock Sterling WebSocket TypeScript client
    and capturing Alloy instance JSON output.
    
    Assumes the Forge/Sterling server is already running.
    """
    
    DEFAULT_PORT = 4000
    TIMEOUT_SECONDS = 30
    
    def __init__(self, port: int = DEFAULT_PORT, script_dir: Optional[str] = None):
        """
        Initialize the client.
        
        Args:
            port: Port where the Forge/Sterling server is running
            script_dir: Directory containing start.sh (defaults to mock_sterling/)
        """
        self.port = port
        self.script_dir = script_dir or self._get_default_script_dir()
        self.start_script = os.path.join(self.script_dir, "start.sh")
        
        if not os.path.exists(self.start_script):
            raise FileNotFoundError(f"start.sh not found at {self.start_script}")
    
    @staticmethod
    def _get_default_script_dir() -> str:
        """Get the default mock_sterling directory."""
        current_file = Path(__file__).resolve()
        return str(current_file.parent)
    
    async def run_sterling_client(self) -> tuple[int, str, str]:
        """
        Run the TypeScript client to connect to the Forge server
        and retrieve the first Alloy instance.
        
        The client will:
        - Connect to ws://localhost:{port}
        - Request metadata
        - Request the first instance from the first generator
        - Output the parsed alloyDatum as JSON
        
        Returns:
            exit_code: Exit code of the TypeScript process
            stdout: Standard output from the process
            stderr: Standard error from the process
        """
        try:
            # Change to mock_sterling directory and run npm
            exit_code, stdout, stderr = await Subprocess.run(
                "bash",
                "-c",
                f"cd {self.script_dir} && npm run run {self.port}",
                timeout_in_s=self.TIMEOUT_SECONDS,
            )

            return exit_code, stdout, stderr
            
        except TimeoutError:
            raise TimeoutError(f"Error: Client timeout after {self.TIMEOUT_SECONDS}s")
        except Exception as e:
            raise Exception(f"Error running client: {e}")
    
    @staticmethod
    def extract_alloy_json(self, stdout: str) -> Dict[str, Any]:
        """
        Extract the Alloy instance JSON from stdout.
        
        The TypeScript client uses pino logger with pino-pretty formatting.
        The output includes multiple log lines, and the alloyDatum JSON is
        pretty-printed across multiple lines starting with "[timestamp] INFO: {"
        
        Args:
            stdout: Raw stdout from the TypeScript process
            
        Returns:
            Parsed alloyDatum object or raises ValueError if not found.
        """
        # Strategy: Find the multi-line JSON block in pino-pretty output
        # Look for a line that starts with timestamp and "INFO: {" 
        # Then collect lines until we have a complete JSON object
        
        lines = stdout.split('\n')
        json_buffer = []
        in_json_block = False
        brace_count = 0
        
        for line in lines:
            # Check if this line starts a JSON block
            # Format: "[HH:MM:SS:mmm] INFO: {"
            if 'INFO: {' in line and not in_json_block:
                # Extract the JSON part (after "INFO: ")
                info_index = line.find('INFO: ')
                if info_index != -1:
                    json_part = line[info_index + 6:]  # Skip "INFO: "
                    json_buffer.append(json_part)
                    in_json_block = True
                    brace_count = json_part.count('{') - json_part.count('}')
            elif in_json_block:
                # We're in a JSON block, add this line
                json_buffer.append(line)
                brace_count += line.count('{') - line.count('}')
                
                # Check if we've closed all braces
                if brace_count == 0:
                    # Try to parse the accumulated JSON
                    json_str = '\n'.join(json_buffer)
                    try:
                        data = json.loads(json_str)
                        if self._is_alloy_datum(data):
                            return data
                    except json.JSONDecodeError:
                        pass
                    
                    # Reset for next potential JSON block
                    json_buffer = []
                    in_json_block = False
        
        # If no valid alloyDatum found, print debug info
        print("Warning: No valid alloyDatum JSON found in output")
        print(f"Output preview (last 500 chars):\n{stdout[-500:]}")
        raise ValueError("No valid alloyDatum JSON found")
    
    @staticmethod
    def _is_alloy_datum(data: Any) -> bool:
        """
        Check if data matches the expected alloyDatumSchema structure.
        
        Schema (from schemas.ts):
        {
            alloy: {
                instance: {
                    sig: array or single object,
                    field: array or single object,
                    bitwidth: number,
                    maxseq: number (optional),
                    command: string,
                    filename: string,
                    version: string
                },
                source: undefined or { filename, content },
                builddate: string
            }
        }
        """
        if not isinstance(data, dict):
            return False
        
        if 'alloy' not in data:
            return False
        
        alloy = data['alloy']
        if not isinstance(alloy, dict):
            return False
        
        if 'instance' not in alloy:
            return False
        
        instance = alloy['instance']
        if not isinstance(instance, dict):
            return False
        
        # Check for required instance fields
        required_fields = ['sig', 'field', 'bitwidth', 'command', 'filename', 'version']
        return all(field in instance for field in required_fields)


async def main():
    """
    Main test function demonstrating usage.
    
    NOTE: This assumes a Forge/Sterling server is already running on port 4000.
    """
    print("=" * 60)
    print("Mock Sterling Client Test")
    print("=" * 60)
    print("\n⚠️  IMPORTANT: Ensure Forge/Sterling server is running on port 4000")
    print("   before running this test.\n")
    
    # Initialize client
    port = 4000
    print(f"Connecting to Forge/Sterling server on port {port}...")
    
    client = MockSterlingClient(port=port)
    
    # Get Alloy instance from the running server
    print("Requesting Alloy instance via WebSocket client...")
    alloy_instance = await client.run_sterling_client()
    
    if alloy_instance:
        print("\n✅ Successfully retrieved Alloy instance!")
        print("\nInstance structure:")
        print(json.dumps(alloy_instance, indent=2))
        
        # Extract useful information
        instance = alloy_instance.get('alloy', {}).get('instance', {})
        print(f"\n📋 Metadata:")
        print(f"  Command: {instance.get('command')}")
        print(f"  Filename: {instance.get('filename')}")
        print(f"  Bitwidth: {instance.get('bitwidth')}")
        print(f"  Version: {instance.get('version')}")
        
        # Check for sigs
        sigs = instance.get('sig', [])
        if not isinstance(sigs, list):
            sigs = [sigs]
        print(f"\n  Signatures: {len(sigs)} total")
        
    else:
        print("\n❌ Failed to retrieve Alloy instance")
        print("\nPossible issues:")
        print("  - Forge/Sterling server not running on port 4000")
        print("  - No instances available for the loaded constraints")
        print("  - WebSocket connection failed")
        return 1
    
    print("\n" + "=" * 60)
    return 0

if __name__ == "__main__":
    exit_code = asyncio.run(main())
    exit(exit_code)
