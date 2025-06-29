#!/usr/bin/env python3

import asyncio
import time
import logging
import sys
import os

# Configure logging to show timestamps
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

async def test_parallelism():
    """Test if parallelism is working correctly"""
    print("=== Parallelism Test ===")
    print("This test will run 3 examples and check if they start processing simultaneously.")
    print("Expected behavior: All examples should start within ~1 second of each other.")
    print()
    
    # Run the plan refinement program with 3 examples
    cmd = [
        "python3", "iterative_plan_refinement_parallel.py",
        "--task", "calendar",
        "--model", "meta-llama/Llama-3.1-8B-Instruct",
        "--end", "3",
        "--max_passes", "1"  # Only run 1 pass to make it quick
    ]
    
    print(f"Running command: {' '.join(cmd)}")
    print()
    
    # Start the process
    start_time = time.time()
    process = await asyncio.create_subprocess_exec(
        *cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE
    )
    
    # Collect output lines
    start_times = []
    example_starts = []
    
    async def read_output(stream, is_stderr=False):
        async for line in stream:
            line_str = line.decode('utf-8').strip()
            if line_str:
                print(line_str)
                
                # Track when examples start processing
                if "Starting processing with model" in line_str:
                    example_id = line_str.split('[')[1].split(']')[0]
                    current_time = time.time() - start_time
                    start_times.append(current_time)
                    example_starts.append((example_id, current_time))
                    print(f"  → {example_id} started at {current_time:.2f}s")
    
    # Read stdout and stderr concurrently
    await asyncio.gather(
        read_output(process.stdout),
        read_output(process.stderr, True)
    )
    
    # Wait for process to complete
    await process.wait()
    
    print()
    print("=== Parallelism Analysis ===")
    
    if len(example_starts) >= 2:
        # Calculate time differences between starts
        time_diffs = []
        for i in range(1, len(start_times)):
            diff = start_times[i] - start_times[i-1]
            time_diffs.append(diff)
        
        avg_diff = sum(time_diffs) / len(time_diffs) if time_diffs else 0
        max_diff = max(time_diffs) if time_diffs else 0
        
        print(f"Number of examples that started: {len(example_starts)}")
        print(f"Start times: {[f'{t:.2f}s' for t in start_times]}")
        print(f"Time differences between starts: {[f'{d:.2f}s' for d in time_diffs]}")
        print(f"Average time between starts: {avg_diff:.2f}s")
        print(f"Maximum time between starts: {max_diff:.2f}s")
        
        # Determine if parallelism is working
        if max_diff < 2.0:  # If examples start within 2 seconds of each other
            print("✅ PARALLELISM WORKING: Examples started processing simultaneously!")
            print("   (All examples started within 2 seconds of each other)")
        else:
            print("❌ PARALLELISM NOT WORKING: Examples started sequentially.")
            print("   (Examples took more than 2 seconds between starts)")
    else:
        print("❌ INSUFFICIENT DATA: Not enough examples started to test parallelism.")
    
    print()
    print("=== Expected vs Actual ===")
    print("Expected: All examples should start within ~1-2 seconds of each other")
    print("Actual: See analysis above")
    
    return process.returncode

if __name__ == "__main__":
    # Change to the source directory
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    
    # Run the test
    exit_code = asyncio.run(test_parallelism())
    sys.exit(exit_code) 