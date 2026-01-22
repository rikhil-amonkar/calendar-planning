#!/usr/bin/env python3
"""
Code generation inference script for Natural Plan problems with iterative refinement.
Uses a prompting strategy to get the model to generate code, then executes it.
If there's a code error or no plan, it gives feedback and tries again (up to 5 iterations).
"""

import os
import re
import json
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from datetime import datetime
from openai import OpenAI
from dotenv import load_dotenv
import pandas as pd
from tqdm import tqdm

from dataset_loader import NaturalPlanDataset, TaskType

load_dotenv()


class CodeGenerationInferenceIterations:
    """Run code generation inference on Natural Plan problems with iterative refinement."""
    
    def __init__(self, 
                 model: str = "gpt-4",
                 prompt_strategy_file: str = "prompt_strategy.txt",
                 timeout: int = 30,
                 max_iterations: int = 5):
        """
        Initialize the code generation inference system.
        
        Args:
            model: Model to use (OpenAI or Deepseek)
            prompt_strategy_file: Path to file containing prompting strategy
            timeout: Timeout for code execution in seconds
            max_iterations: Maximum number of iterations per problem
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
        self.timeout = timeout
        self.max_iterations = max_iterations
        self.dataset = NaturalPlanDataset()
        
        # Load prompting strategy
        self.prompt_strategy = self._load_prompt_strategy()
    
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
    
    def create_prompt(self, problem_text: str) -> str:
        """
        Create the full prompt by combining strategy and problem.
        
        Args:
            problem_text: The problem to solve
        
        Returns:
            Complete prompt with strategy and problem
        """
        # Replace {PROBLEM} placeholder in strategy with actual problem
        prompt = self.prompt_strategy.replace("{PROBLEM}", problem_text)
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
    
    def has_code_error(self, exec_success: bool, stderr: str, stdout: str) -> bool:
        """
        Check if code execution had an error.
        
        Args:
            exec_success: Whether execution succeeded
            stderr: Error output
            stdout: Standard output
        
        Returns:
            True if there was a code error
        """
        if not exec_success:
            return True
        
        # Check for error indicators in output
        error_indicators = ['Traceback', 'Error', 'Exception', 'SyntaxError', 
                          'NameError', 'TypeError', 'ValueError', 'AttributeError']
        
        error_text = (stderr + " " + stdout).lower()
        return any(indicator.lower() in error_text for indicator in error_indicators)
    
    def has_no_plan(self, output: str) -> bool:
        """
        Check if the output has no plan (empty or invalid output).
        
        A "no plan" output means the code ran successfully but produced no valid
        itinerary/plan. This is different from a code error.
        
        Args:
            output: Code execution output
        
        Returns:
            True if there's no plan in the output
        """
        if not output or not output.strip():
            return True
        
        # Check for common "no plan" indicators in the output text
        output_lower = output.lower()
        no_plan_indicators = [
            'no plan',
            'no solution',
            'no feasible',
            'impossible',
            'cannot find',
            'unable to find',
            'no valid',
            'empty solution',
        ]
        
        # Check if output indicates no plan was found
        if any(indicator in output_lower for indicator in no_plan_indicators):
            return True
        
        # Check if output is just an empty JSON structure
        output_stripped = output.strip()
        if output_stripped in ['[]', '{}', '{"itinerary": []}', '{"itinerary":[]}']:
            return True
        
        # Check if output looks like it might be a JSON with empty itinerary
        # This is a heuristic - the structured converter will parse it more carefully
        if 'itinerary' in output_lower and ('[]' in output_stripped or 'empty' in output_lower):
            return True
        
        # If output is very short, it might not contain a plan
        # But be careful - some valid outputs might be short
        # This is a fallback check
        if len(output_stripped) < 20 and 'meet' not in output_lower:
            return True
        
        return False
    
    def create_feedback_prompt(self, original_prompt: str, iteration: int, 
                               previous_code: str, error: Optional[str] = None,
                               output: Optional[str] = None, has_error: bool = False,
                               has_no_plan: bool = False) -> str:
        """
        Create a feedback prompt for subsequent iterations.
        
        The feedback includes the original prompt plus error information and the code that failed.
        
        Args:
            original_prompt: The original problem prompt
            iteration: Current iteration number
            previous_code: Code from previous iteration
            error: Error message if there was an error
            output: Output from previous iteration if no error
            has_error: Whether there was a code error
            has_no_plan: Whether there was no plan
        
        Returns:
            Feedback prompt for the next iteration
        """
        feedback_parts = [original_prompt]
        feedback_parts.append("\n")
        
        if has_error:
            feedback_parts.append("The code you generated had an error when executed.")
            if error:
                feedback_parts.append(f"\nError message:\n{error}")
            feedback_parts.append(f"\nThis is the code that caused the error:\n```python\n{previous_code}\n```")
            feedback_parts.append("\nPlease fix the code to eliminate the error and solve the problem correctly.")
        elif has_no_plan:
            feedback_parts.append("The code you generated ran successfully but produced no valid plan.")
            if output:
                feedback_parts.append(f"\nOutput from your code:\n{output}")
            feedback_parts.append(f"\nThis is the code that produced no plan:\n```python\n{previous_code}\n```")
            feedback_parts.append("\nPlease revise the code to generate a valid plan that meets the requirements.")
        
        return "\n".join(feedback_parts)
    
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
            Dictionary with results including all iterations
        """
        # Load problem
        problem = self.dataset.get_problem(task_type, problem_index, split)
        problem_text = self.dataset.format_problem(problem, shot_type)
        golden_solution = self.dataset.get_golden_solution(problem)
        
        # Create initial prompt
        original_prompt = self.create_prompt(problem_text)
        
        # Store all iterations
        iterations = []
        current_prompt = original_prompt
        
        for iteration_num in range(1, self.max_iterations + 1):
            iteration_result = {
                "iteration": iteration_num,
                "prompt": current_prompt,
            }
            
            # Get model response
            try:
                # Prepare API params
                api_params = {
                    "model": self.model,
                    "messages": [{"role": "user", "content": current_prompt}]
                }

                # Special handling for O3-mini models:
                # - Always pass reasoning_effort="high" when the model name begins with "o3-mini"
                if self.model.lower().startswith("o3-mini"):
                    api_params["reasoning_effort"] = "high"
                
                # Don't add temperature for reasoning models (O1, O3, GPT-5, Deepseek-Reasoner)
                reasoning_models = ["o1", "o3", "gpt-5", "deepseek-reasoner"]
                if not any(self.model.lower().startswith(prefix) for prefix in reasoning_models):
                    api_params["temperature"] = 0.7
                
                response = self.client.chat.completions.create(**api_params)
                model_response = response.choices[0].message.content
                
            except Exception as e:
                iteration_result.update({
                    "success": False,
                    "error": f"API error: {str(e)}",
                    "model_response": None,
                    "code": None,
                    "execution_success": False,
                    "output": None,
                    "error_output": None,
                    "has_code_error": False,
                    "has_no_plan": False,
                    "should_continue": False
                })
                iterations.append(iteration_result)
                break  # Stop if API error
            
            # Extract code
            code = self.extract_code(model_response)
            
            if code is None:
                iteration_result.update({
                    "success": False,
                    "error": "No code found in response",
                    "model_response": model_response,
                    "code": None,
                    "execution_success": False,
                    "output": None,
                    "error_output": None,
                    "has_code_error": True,  # Treat as error
                    "has_no_plan": False,
                    "should_continue": True  # Try again
                })
                iterations.append(iteration_result)
                # Create feedback for next iteration
                feedback = f"{original_prompt}\n\nNo code was found in your response. Please provide working Python code to solve this problem."
                current_prompt = feedback
                continue  # Try next iteration
            
            # Execute code
            exec_success, stdout, stderr = self.execute_code(code, problem)
            
            # Check for code errors
            has_error = self.has_code_error(exec_success, stderr, stdout)
            
            # Check for no plan (only if no error)
            has_no_plan_flag = False
            if not has_error and exec_success:
                has_no_plan_flag = self.has_no_plan(stdout)
            
            iteration_result.update({
                "success": True,
                "error": None,
                "model_response": model_response,
                "code": code,
                "execution_success": exec_success,
                "output": stdout,
                "error_output": stderr,
                "has_code_error": has_error,
                "has_no_plan": has_no_plan_flag,
                "should_continue": has_error or has_no_plan_flag
            })
            
            iterations.append(iteration_result)
            
            # If we have a properly formatted output (no error, has plan), stop
            if not has_error and not has_no_plan_flag:
                break
            
            # If this was the last iteration, stop anyway
            if iteration_num >= self.max_iterations:
                break
            
            # Create feedback prompt for next iteration
            # Include original prompt + feedback
            current_prompt = self.create_feedback_prompt(
                original_prompt=original_prompt,
                iteration=iteration_num,
                previous_code=code,
                error=stderr if has_error else None,  # Error message only if there's an error
                output=stdout if not has_error else None,  # Output only if no error
                has_error=has_error,
                has_no_plan=has_no_plan_flag
            )
        
        # Determine final status
        final_iteration = iterations[-1] if iterations else None
        num_iterations = len(iterations)
        
        # Get final iteration results
        if final_iteration:
            final_exec_success = final_iteration.get("execution_success", False)
            final_output = final_iteration.get("output", "")
            final_has_error = final_iteration.get("has_code_error", False)
            final_has_no_plan = final_iteration.get("has_no_plan", False)
        else:
            final_exec_success = False
            final_output = ""
            final_has_error = True
            final_has_no_plan = False
        
        return {
            "task_type": task_type,
            "problem_index": problem_index,
            "problem_id": problem.get("id"),
            "success": final_iteration.get("success", False) if final_iteration else False,
            "error": final_iteration.get("error") if final_iteration else "No iterations completed",
            "model_response": final_iteration.get("model_response") if final_iteration else None,
            "code": final_iteration.get("code") if final_iteration else None,
            "execution_success": final_exec_success,
            "output": final_output,
            "error_output": final_iteration.get("error_output") if final_iteration else None,
            "golden_solution": golden_solution,
            "model": self.model,
            "timestamp": datetime.now().isoformat(),
            "num_iterations": num_iterations,
            "iterations": iterations,
            "final_has_code_error": final_has_error,
            "final_has_no_plan": final_has_no_plan
        }
    
    def run_batch_inference(self,
                           task_type: TaskType,
                           problem_indices: List[int],
                           split: str = "train",
                           shot_type: str = "0shot",
                           save_results: bool = True,
                           experiment_name: Optional[str] = None) -> pd.DataFrame:
        """
        Run inference on multiple problems with iterative refinement.
        
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
        print(f"Code Generation Inference (Iterative Refinement)")
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
        
        # Create DataFrame (flatten some fields for compatibility)
        df_data = []
        for result in results:
            row = {k: v for k, v in result.items() if k != 'iterations'}
            row['num_iterations'] = result.get('num_iterations', 0)
            df_data.append(row)
        
        df = pd.DataFrame(df_data)
        
        # Print summary
        print(f"\n{'='*70}")
        print("SUMMARY")
        print(f"{'='*70}")
        print(f"Total problems: {len(results)}")
        print(f"API success: {df['success'].sum()} / {len(results)}")
        print(f"Code extracted: {df['code'].notna().sum()} / {len(results)}")
        print(f"Code executed successfully: {df['execution_success'].sum()} / {len(results)}")
        
        # Iteration statistics
        total_iterations = sum(result.get('num_iterations', 0) for result in results)
        avg_iterations = total_iterations / len(results) if results else 0
        problems_with_multiple_iterations = sum(1 for result in results if result.get('num_iterations', 0) > 1)
        
        print(f"\nIteration Statistics:")
        print(f"  Total iterations: {total_iterations}")
        print(f"  Average iterations per problem: {avg_iterations:.2f}")
        print(f"  Problems with multiple iterations: {problems_with_multiple_iterations}")
        print(f"{'='*70}\n")
        
        # Save results
        if save_results:
            if experiment_name is None:
                experiment_name = f"code_gen_iterations_{task_type}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
            
            # Save to new_results folder inside improved directory
            results_dir = Path(__file__).parent / "new_results"
            results_dir.mkdir(exist_ok=True)
            
            # Save CSV (without iterations detail for compatibility)
            csv_path = results_dir / f"{experiment_name}.csv"
            df.to_csv(csv_path, index=False)
            print(f"✓ Results saved to: {csv_path}")
            
            # Save detailed JSON (with all iterations)
            json_path = results_dir / f"{experiment_name}.json"
            with open(json_path, 'w') as f:
                json.dump(results, f, indent=2)
            print(f"✓ Detailed results saved to: {json_path}")
        
        return df


def main():
    """Example usage."""
    import sys
    
    # Parse arguments
    model = sys.argv[1] if len(sys.argv) > 1 else "gpt-4"
    strategy_file = sys.argv[2] if len(sys.argv) > 2 else "prompt_strategy.txt"
    task_type = sys.argv[3] if len(sys.argv) > 3 else "meeting"
    num_problems = int(sys.argv[4]) if len(sys.argv) > 4 else 100
    
    print(f"\n{'='*70}")
    print("Code Generation Inference (Iterative Refinement) - Test Split")
    print(f"{'='*70}")
    print(f"Task: {task_type}")
    print(f"Problems: {num_problems}")
    print(f"{'='*70}\n")
    
    # Check if strategy file exists
    if not Path(strategy_file).exists():
        print(f"⚠ Strategy file not found: {strategy_file}")
        print("\nCreating example strategy file...")
        
        example_strategy = """You are an expert Python programmer. I will give you a planning problem.

Your task:
1. Write Python code to solve the problem
2. The code should print the final answer
3. Use clear, working Python code

Problem:
{PROBLEM}

Please provide working Python code to solve this problem. Format your code in a ```python code block."""
        
        with open(strategy_file, 'w') as f:
            f.write(example_strategy)
        
        print(f"✓ Created example strategy: {strategy_file}")
        print("✓ Edit this file with your own prompting strategy\n")
    
    # Initialize inference system
    inference = CodeGenerationInferenceIterations(
        model=model,
        prompt_strategy_file=strategy_file,
        max_iterations=5
    )
    
    # Run on test problems only
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    experiment_name = f"{task_type}_test_iterations_{model.replace('.', '_')}_{timestamp}"
    
    df = inference.run_batch_inference(
        task_type=task_type,
        problem_indices=range(num_problems),
        split="test",                 # Use test split only
        shot_type="0shot",
        experiment_name=experiment_name
    )
    
    # Show some results
    print("\nExample Results:")
    print(df[["problem_id", "success", "execution_success", "num_iterations"]].to_string(index=False))


if __name__ == "__main__":
    main()
