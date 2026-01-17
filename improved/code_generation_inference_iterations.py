#!/usr/bin/env python3
"""
Code generation inference script for Natural Plan problems with iterative refinement.
Uses a prompting strategy to get the model to generate code, then executes it.
If code execution fails or produces no plan, provides feedback for up to max_iterations attempts.
"""

import os
import re
import json
import subprocess
import tempfile
import argparse
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from datetime import datetime
from openai import OpenAI
from dotenv import load_dotenv
import pandas as pd
from tqdm import tqdm

load_dotenv()

# Type alias for task type (since we're using a specific JSON file)
TaskType = str


class CodeGenerationInferenceIterations:
    """Run code generation inference on Natural Plan problems with iterative refinement."""
    
    def __init__(self, 
                 model: str = "gpt-4",
                 prompt_strategy_file: str = "prompt_strategy.txt",
                 dataset_file: str = "../data/meeting_planning_100.json",
                 timeout: int = 30,
                 max_iterations: int = 5):
        """
        Initialize the code generation inference system.
        
        Args:
            model: Model to use (OpenAI or Deepseek)
            prompt_strategy_file: Path to file containing prompting strategy
            dataset_file: Path to JSON file containing meeting planning problems
            timeout: Timeout for code execution in seconds
            max_iterations: Maximum number of iterations if code fails or produces no plan
        """
        # Initialize appropriate API client based on model
        if model.startswith("deepseek-"):
            # Use Deepseek API
            self.client = OpenAI(
                api_key=os.getenv("DEEPSEEK_API_KEY"),
                base_url="https://api.deepseek.com"
            )
            self.api_provider = "deepseek"
        else:
            # Use OpenAI API
            self.client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
            self.api_provider = "openai"
        
        self.model = model
        self.prompt_strategy_file = prompt_strategy_file
        self.dataset_file = dataset_file
        self.timeout = timeout
        self.max_iterations = max_iterations
        
        # Load dataset from JSON file
        self.dataset = self._load_dataset()
        
        # Get sorted list of problem keys for indexing
        self.problem_keys = sorted(self.dataset.keys())
        
        # Load prompting strategy
        self.prompt_strategy = self._load_prompt_strategy()
    
    def _load_dataset(self) -> Dict:
        """Load the dataset from JSON file."""
        dataset_path = Path(self.dataset_file)
        
        if not dataset_path.exists():
            raise FileNotFoundError(f"Dataset file not found: {self.dataset_file}")
        
        with open(dataset_path, 'r') as f:
            dataset = json.load(f)
        
        print(f"✓ Loaded dataset from: {self.dataset_file}")
        print(f"  Total problems: {len(dataset)}\n")
        
        return dataset
    
    def _load_prompt_strategy(self) -> str:
        """Load the prompting strategy from file."""
        strategy_path = Path(self.prompt_strategy_file)
        
        if not strategy_path.exists():
            raise FileNotFoundError(f"Prompt strategy file not found: {self.prompt_strategy_file}")
        
        with open(strategy_path, 'r') as f:
            strategy = f.read()
        
        print(f"✓ Loaded prompt strategy from: {self.prompt_strategy_file}")
        print(f"  Length: {len(strategy)} characters\n")
        
        return strategy
    
    def create_prompt(self, problem_text: str, accumulated_feedback: Optional[str] = None) -> str:
        """
        Create the full prompt by combining strategy and problem.
        
        Args:
            problem_text: The problem to solve
            accumulated_feedback: Feedback from previous iterations (if any)
        
        Returns:
            Complete prompt with strategy, problem, and accumulated feedback
        """
        # Replace {PROBLEM} placeholder in strategy with actual problem
        prompt = self.prompt_strategy.replace("{PROBLEM}", problem_text)
        
        # Append accumulated feedback if present
        if accumulated_feedback:
            prompt = prompt + "\n\n" + accumulated_feedback
        
        return prompt
    
    def extract_code(self, response: str) -> Optional[str]:
        """
        Extract code from the model's response.
        
        Looks for code in markdown code blocks (```python ... ```).
        
        Args:
            response: Model's response text
        
        Returns:
            Extracted code or None if no code found
        """
        # Pattern 1: ```python ... ```
        pattern1 = r'```python\s*(.*?)```'
        matches = re.findall(pattern1, response, re.DOTALL)
        
        if matches:
            return matches[0].strip()
        
        # Pattern 2: ``` ... ``` (without language specification)
        pattern2 = r'```\s*(.*?)```'
        matches = re.findall(pattern2, response, re.DOTALL)
        
        if matches:
            # Return the largest code block
            return max(matches, key=len).strip()
        
        # Pattern 3: Look for code between common markers
        pattern3 = r'(?:def |class |import |from )(.*?)(?:\n\n|$)'
        matches = re.findall(pattern3, response, re.DOTALL)
        
        if matches:
            return matches[0].strip()
        
        return None
    
    def execute_code(self, code: str, problem_data: Dict) -> Tuple[bool, str, str]:
        """
        Execute the generated code and capture output.
        
        Args:
            code: Python code to execute
            problem_data: Problem data (for potential use in code)
        
        Returns:
            Tuple of (success, stdout, stderr)
        """
        # Create a temporary file with the code
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            temp_file = f.name
            
            # Add problem data as a comment/variable at the top
            f.write(f"# Problem ID: {problem_data.get('id', 'unknown')}\n\n")
            f.write(code)
        
        try:
            # Execute the code with timeout
            result = subprocess.run(
                ['python', temp_file],
                capture_output=True,
                text=True,
                timeout=self.timeout
            )
            
            success = result.returncode == 0
            stdout = result.stdout.strip()
            stderr = result.stderr.strip()
            
            return success, stdout, stderr
            
        except subprocess.TimeoutExpired:
            return False, "", f"Execution timeout ({self.timeout}s)"
        
        except Exception as e:
            return False, "", str(e)
        
        finally:
            # Clean up temporary file
            try:
                os.unlink(temp_file)
            except:
                pass
    
    def _has_execution_error(self, stdout: str, stderr: str) -> bool:
        """
        Check if the code execution produced an error.
        
        Args:
            stdout: Standard output
            stderr: Standard error
        
        Returns:
            True if there's an execution error
        """
        if stderr:
            return True
        
        error_indicators = ["Error", "Exception", "Traceback"]
        output_text = (stdout or "").lower()
        return any(indicator.lower() in output_text for indicator in error_indicators)
    
    def _has_no_plan(self, stdout: str, stderr: str, exec_success: bool) -> bool:
        """
        Check if the code produced no plan (empty output or no meaningful output).
        
        Args:
            stdout: Standard output
            stderr: Standard error
            exec_success: Whether execution was successful
        
        Returns:
            True if there's no plan in the output
        """
        # If execution failed, we don't check for empty plan (that's handled as error)
        if not exec_success or self._has_execution_error(stdout, stderr):
            return False
        
        # Check if output is empty or just whitespace
        if not stdout or not stdout.strip():
            return True
        
        # Could add more sophisticated plan detection here if needed
        return False
    
    def run_single_inference(self, 
                            task_type: TaskType, 
                            problem_index: int,
                            split: str = "train",
                            shot_type: str = "0shot") -> Dict:
        """
        Run inference on a single problem with iterative refinement.
        
        Args:
            task_type: Type of task
            problem_index: Index of the problem
            split: Data split
            shot_type: "0shot" or "5shot"
        
        Returns:
            Dictionary with results
        """
        # Load problem from JSON dataset
        # Map problem_index to sorted keys (ignoring split since we have all problems)
        if problem_index >= len(self.problem_keys):
            return {
                "task_type": task_type,
                "problem_index": problem_index,
                "problem_id": None,
                "success": False,
                "error": f"Problem index {problem_index} out of range (max: {len(self.problem_keys) - 1})",
                "model_response": None,
                "code": None,
                "execution_success": False,
                "output": None,
                "golden_solution": None,
                "iterations": [],
                "iteration_count": 0,
                "model": self.model,
                "timestamp": datetime.now().isoformat()
            }
        
        problem_key = self.problem_keys[problem_index]
        problem = self.dataset[problem_key]
        
        # Get problem text based on shot_type (prompt_0shot or prompt_5shot)
        prompt_key = f"prompt_{shot_type}"
        if prompt_key not in problem:
            return {
                "task_type": task_type,
                "problem_index": problem_index,
                "problem_id": problem_key,
                "success": False,
                "error": f"Shot type '{shot_type}' not found (available: prompt_0shot, prompt_5shot)",
                "model_response": None,
                "code": None,
                "execution_success": False,
                "output": None,
                "golden_solution": None,
                "iterations": [],
                "iteration_count": 0,
                "model": self.model,
                "timestamp": datetime.now().isoformat()
            }
        
        problem_text = problem[prompt_key]
        golden_solution = problem.get("golden_plan", [])
        
        # Initialize tracking variables
        accumulated_feedback = None
        all_iterations = []
        final_code = None
        final_model_response = None
        final_exec_success = False
        final_stdout = None
        final_stderr = None
        
        # Iterate up to max_iterations
        for iteration in range(1, self.max_iterations + 1):
            # Create prompt with accumulated feedback
            full_prompt = self.create_prompt(problem_text, accumulated_feedback)
            
            # Get model response
            try:
                # Prepare API params
                api_params = {
                    "model": self.model,
                    "messages": [{"role": "user", "content": full_prompt}]
                }
                
                # Don't add temperature for reasoning models (O1, O3, GPT-5, Deepseek-Reasoner) - they only support default temperature
                reasoning_models = ["o1", "o3", "gpt-5", "deepseek-reasoner"]
                if not any(self.model.lower().startswith(prefix) for prefix in reasoning_models):
                    api_params["temperature"] = 0.7
                
                # Special handling for o3-mini-2025-01-31: set reasoning_effort to "high"
                if self.model.lower() == "o3-mini-2025-01-31":
                    api_params["reasoning_effort"] = "high"
                
                response = self.client.chat.completions.create(**api_params)
                model_response = response.choices[0].message.content
                
            except Exception as e:
                return {
                    "task_type": task_type,
                    "problem_index": problem_index,
                    "problem_id": problem_key,
                    "success": False,
                    "error": f"API error: {str(e)}",
                    "model_response": None,
                    "code": None,
                    "execution_success": False,
                    "output": None,
                    "golden_solution": golden_solution,
                    "iterations": all_iterations,
                    "iteration_count": iteration - 1,
                    "model": self.model,
                    "timestamp": datetime.now().isoformat()
                }
            
            # Extract code
            code = self.extract_code(model_response)
            
            if code is None:
                return {
                    "task_type": task_type,
                    "problem_index": problem_index,
                    "problem_id": problem_key,
                    "success": False,
                    "error": "No code found in response",
                    "model_response": model_response,
                    "code": None,
                    "execution_success": False,
                    "output": None,
                    "golden_solution": golden_solution,
                    "iterations": all_iterations,
                    "iteration_count": iteration,
                    "model": self.model,
                    "timestamp": datetime.now().isoformat()
                }
            
            # Execute code (pass problem with key for ID)
            problem_with_id = problem.copy()
            problem_with_id['id'] = problem_key
            exec_success, stdout, stderr = self.execute_code(code, problem_with_id)
            
            # Check for execution errors
            has_execution_error = self._has_execution_error(stdout, stderr) or not exec_success
            
            # Check for empty plan
            has_no_plan = self._has_no_plan(stdout, stderr, exec_success)
            
            # Determine why we stopped (if we do stop)
            stopped_reason = None
            will_retry = (has_execution_error or has_no_plan) and (iteration < self.max_iterations)
            
            # Determine stopping reason
            if not has_execution_error and not has_no_plan:
                # Code executed successfully and produced output - stop iterations
                stopped_reason = "successful_execution"
            elif iteration >= self.max_iterations:
                # Reached max iterations
                stopped_reason = "max_iterations_reached"
            else:
                # Will retry, no stop reason yet
                stopped_reason = None
            
            # Store results for this iteration (with comprehensive info)
            iteration_result = {
                "iteration": iteration,  # Attempt number (1, 2, 3, ...)
                "code": code,
                "model_response": model_response,
                "execution_success": exec_success,
                "has_execution_error": has_execution_error,
                "has_no_plan": has_no_plan,
                "output": stdout,
                "error_output": stderr,
                "will_retry": will_retry,  # Whether another attempt will be made
                "stopped_reason": stopped_reason  # Why iterations stopped (if applicable)
            }
            all_iterations.append(iteration_result)
            
            # Store final results (from this iteration)
            final_code = code
            final_model_response = model_response
            final_exec_success = exec_success
            final_stdout = stdout
            final_stderr = stderr
            
            # Only continue if there's an execution error or no plan
            # If code executed successfully and produced output (even if wrong), stop
            if not has_execution_error and not has_no_plan:
                # Code executed successfully and produced output - stop iterations
                break
            
            # Prepare feedback for next iteration (if we haven't reached max_iterations)
            if iteration < self.max_iterations:
                if has_execution_error:
                    feedback_parts = [
                        f"--- Iteration {iteration} Feedback ---",
                        f"Previous code execution failed with error:\n{stderr if stderr else stdout}",
                        f"\nGenerated code that caused the error:\n```python\n{code}\n```",
                        "\nPlease fix the code to eliminate execution errors."
                    ]
                else:  # has_no_plan
                    feedback_parts = [
                        f"--- Iteration {iteration} Feedback ---",
                        "The generated code ran successfully but produced no valid plan.",
                        f"\nCode output:\n{stdout if stdout else '(empty)'}",
                        f"\nGenerated code:\n```python\n{code}\n```",
                        "\nPlease revise the code to generate a valid plan that meets the requirements."
                    ]
                
                new_feedback = "\n".join(feedback_parts)
                
                # Accumulate feedback
                if accumulated_feedback:
                    accumulated_feedback = accumulated_feedback + "\n\n" + new_feedback
                else:
                    accumulated_feedback = new_feedback
        
        # Determine final status
        final_has_error = self._has_execution_error(final_stdout, final_stderr) if final_stdout or final_stderr else False
        final_has_no_plan = self._has_no_plan(final_stdout, final_stderr, final_exec_success) if final_stdout is not None else False
        
        # Return final results with comprehensive iteration tracking
        return {
            "task_type": task_type,
            "problem_index": problem_index,
            "problem_id": problem_key,
            "success": True,
            "error": None,
            # Final iteration results (backward compatibility with original format)
            "model_response": final_model_response,
            "code": final_code,
            "execution_success": final_exec_success,
            "output": final_stdout,
            "error_output": final_stderr,
            # Iteration tracking
            "iterations": all_iterations,  # List of all attempts with full details
            "iteration_count": len(all_iterations),  # Total number of attempts made
            "max_iterations": self.max_iterations,  # Maximum allowed iterations
            "final_has_execution_error": final_has_error,
            "final_has_no_plan": final_has_no_plan,
            # Other metadata
            "golden_solution": golden_solution,
            "model": self.model,
            "timestamp": datetime.now().isoformat()
        }
    
    def run_batch_inference(self,
                           task_type: TaskType,
                           problem_indices: List[int],
                           split: str = "train",
                           shot_type: str = "0shot",
                           save_results: bool = True,
                           experiment_name: Optional[str] = None) -> pd.DataFrame:
        """
        Run inference on multiple problems.
        
        Args:
            task_type: Type of task
            problem_indices: List of problem indices
            split: Data split
            shot_type: "0shot" or "5shot"
            save_results: Whether to save results
            experiment_name: Name for saving results
        
        Returns:
            DataFrame with results
        """
        print(f"\n{'='*70}")
        print(f"Code Generation Inference with Iterations")
        print(f"{'='*70}")
        print(f"Model: {self.model}")
        print(f"Task: {task_type}")
        print(f"Problems: {len(problem_indices)}")
        print(f"Shot type: {shot_type}")
        print(f"Strategy: {self.prompt_strategy_file}")
        print(f"Max iterations: {self.max_iterations}")
        print(f"{'='*70}\n")
        
        results = []
        
        for idx in tqdm(problem_indices, desc="Running inference"):
            result = self.run_single_inference(task_type, idx, split, shot_type)
            results.append(result)
        
        # Create DataFrame (flatten iterations data for CSV)
        # For CSV, we'll store just the iteration count and flatten some fields
        flattened_results = []
        for r in results:
            flat_r = r.copy()
            # Store iterations as JSON string for CSV
            if "iterations" in flat_r:
                flat_r["iterations_json"] = json.dumps(flat_r["iterations"])
            flattened_results.append(flat_r)
        
        df = pd.DataFrame(flattened_results)
        
        # Print summary
        print(f"\n{'='*70}")
        print("SUMMARY")
        print(f"{'='*70}")
        print(f"Total problems: {len(results)}")
        print(f"API success: {df['success'].sum()} / {len(results)}")
        print(f"Code extracted: {df['code'].notna().sum()} / {len(results)}")
        print(f"Code executed: {df['execution_success'].sum()} / {len(results)}")
        if 'iteration_count' in df.columns:
            avg_iterations = df['iteration_count'].mean()
            print(f"Average iterations: {avg_iterations:.2f}")
        print(f"{'='*70}\n")
        
        # Save results
        if save_results:
            if experiment_name is None:
                experiment_name = f"code_gen_iter_{task_type}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
            
            results_dir = Path("code_generation_results")
            results_dir.mkdir(exist_ok=True)
            
            # Save CSV (with flattened data)
            csv_path = results_dir / f"{experiment_name}.csv"
            df.to_csv(csv_path, index=False)
            print(f"✓ Results saved to: {csv_path}")
            
            # Save detailed JSON (with full iterations data)
            json_path = results_dir / f"{experiment_name}.json"
            with open(json_path, 'w') as f:
                json.dump(results, f, indent=2)
            print(f"✓ Detailed results saved to: {json_path}")
        
        return df


def main():
    """Example usage."""
    parser = argparse.ArgumentParser(description="Code generation inference with iterative refinement")
    parser.add_argument("model", nargs="?", default="gpt-4", help="Model to use (default: gpt-4)")
    parser.add_argument("strategy_file", nargs="?", default="prompt_strategy.txt", 
                       help="Path to prompt strategy file (default: prompt_strategy.txt)")
    parser.add_argument("task_type", nargs="?", default="meeting", 
                       help="Task type (default: meeting)")
    parser.add_argument("num_problems", nargs="?", type=int, default=100,
                       help="Number of problems to run (default: 100)")
    parser.add_argument("--max-iterations", type=int, default=5,
                       help="Maximum number of iterations if code fails (default: 5)")
    
    args = parser.parse_args()
    
    print(f"\n{'='*70}")
    print("Code Generation Inference with Iterations - Test Split")
    print(f"{'='*70}")
    print(f"Task: {args.task_type}")
    print(f"Problems: {args.num_problems}")
    print(f"Max iterations: {args.max_iterations}")
    print(f"{'='*70}\n")
    
    # Check if strategy file exists
    if not Path(args.strategy_file).exists():
        print(f"⚠ Strategy file not found: {args.strategy_file}")
        print("\nCreating example strategy file...")
        
        example_strategy = """You are an expert Python programmer. I will give you a planning problem.

Your task:
1. Write Python code to solve the problem
2. The code should print the final answer
3. Use clear, working Python code

Problem:
{PROBLEM}

Please provide working Python code to solve this problem. Format your code in a ```python code block."""
        
        with open(args.strategy_file, 'w') as f:
            f.write(example_strategy)
        
        print(f"✓ Created example strategy: {args.strategy_file}")
        print("✓ Edit this file with your own prompting strategy\n")
    
    # Initialize inference system
    inference = CodeGenerationInferenceIterations(
        model=args.model,
        prompt_strategy_file=args.strategy_file,
        max_iterations=args.max_iterations
    )
    
    # Run on test problems only
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    experiment_name = f"{args.task_type}_test_{args.model.replace('.', '_')}_{timestamp}"
    
    df = inference.run_batch_inference(
        task_type=args.task_type,
        problem_indices=range(args.num_problems),
        split="test",                 # Use test split only
        shot_type="0shot",
        experiment_name=experiment_name
    )
    
    # Show some results
    print("\nExample Results:")
    display_cols = ["problem_id", "success", "execution_success"]
    if "iteration_count" in df.columns:
        display_cols.append("iteration_count")
    print(df[display_cols].to_string(index=False))


if __name__ == "__main__":
    main()
