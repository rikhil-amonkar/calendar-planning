#!/usr/bin/env python3
"""
Code generation inference script for Natural Plan problems.
Uses a prompting strategy to get the model to generate code, then executes it.
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


class CodeGenerationInference:
    """Run code generation inference on Natural Plan problems."""
    
    def __init__(self, 
                 model: str = "gpt-4",
                 prompt_strategy_file: str = "prompt_strategy.txt",
                 timeout: int = 30):
        """
        Initialize the code generation inference system.
        
        Args:
            model: Model to use (OpenAI or Deepseek)
            prompt_strategy_file: Path to file containing prompting strategy
            timeout: Timeout for code execution in seconds
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
    
    def run_single_inference(self, 
                            task_type: TaskType, 
                            problem_index: int,
                            split: str = "train",
                            shot_type: str = "0shot") -> Dict:
        """
        Run inference on a single problem.
        
        Args:
            task_type: Type of task
            problem_index: Index of the problem
            split: Data split
            shot_type: "0shot" or "5shot"
        
        Returns:
            Dictionary with results
        """
        # Load problem
        problem = self.dataset.get_problem(task_type, problem_index, split)
        problem_text = self.dataset.format_problem(problem, shot_type)
        golden_solution = self.dataset.get_golden_solution(problem)
        
        # Create prompt
        full_prompt = self.create_prompt(problem_text)
        
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
            
            response = self.client.chat.completions.create(**api_params)
            model_response = response.choices[0].message.content
            
        except Exception as e:
            return {
                "task_type": task_type,
                "problem_index": problem_index,
                "problem_id": problem.get("id"),
                "success": False,
                "error": f"API error: {str(e)}",
                "model_response": None,
                "code": None,
                "execution_success": False,
                "output": None,
                "golden_solution": golden_solution
            }
        
        # Extract code
        code = self.extract_code(model_response)
        
        if code is None:
            return {
                "task_type": task_type,
                "problem_index": problem_index,
                "problem_id": problem.get("id"),
                "success": False,
                "error": "No code found in response",
                "model_response": model_response,
                "code": None,
                "execution_success": False,
                "output": None,
                "golden_solution": golden_solution
            }
        
        # Execute code
        exec_success, stdout, stderr = self.execute_code(code, problem)
        
        return {
            "task_type": task_type,
            "problem_index": problem_index,
            "problem_id": problem.get("id"),
            "success": True,
            "error": None,
            "model_response": model_response,
            "code": code,
            "execution_success": exec_success,
            "output": stdout,
            "error_output": stderr,
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
        print(f"Code Generation Inference")
        print(f"{'='*70}")
        print(f"Model: {self.model}")
        print(f"Task: {task_type}")
        print(f"Problems: {len(problem_indices)}")
        print(f"Shot type: {shot_type}")
        print(f"Strategy: {self.prompt_strategy_file}")
        print(f"{'='*70}\n")
        
        results = []
        
        for idx in tqdm(problem_indices, desc="Running inference"):
            result = self.run_single_inference(task_type, idx, split, shot_type)
            results.append(result)
        
        # Create DataFrame
        df = pd.DataFrame(results)
        
        # Print summary
        print(f"\n{'='*70}")
        print("SUMMARY")
        print(f"{'='*70}")
        print(f"Total problems: {len(results)}")
        print(f"API success: {df['success'].sum()} / {len(results)}")
        print(f"Code extracted: {df['code'].notna().sum()} / {len(results)}")
        print(f"Code executed: {df['execution_success'].sum()} / {len(results)}")
        print(f"{'='*70}\n")
        
        # Save results
        if save_results:
            if experiment_name is None:
                experiment_name = f"code_gen_{task_type}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
            
            results_dir = Path("code_generation_results")
            results_dir.mkdir(exist_ok=True)
            
            # Save CSV
            csv_path = results_dir / f"{experiment_name}.csv"
            df.to_csv(csv_path, index=False)
            print(f"✓ Results saved to: {csv_path}")
            
            # Save detailed JSON
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
    print("Code Generation Inference - Test Split")
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
    inference = CodeGenerationInference(
        model=model,
        prompt_strategy_file=strategy_file
    )
    
    # Run on test problems only
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    experiment_name = f"{task_type}_test_{model.replace('.', '_')}_{timestamp}"
    
    df = inference.run_batch_inference(
        task_type=task_type,
        problem_indices=range(num_problems),
        split="test",                 # Use test split only
        shot_type="0shot",
        experiment_name=experiment_name
    )
    
    # Show some results
    print("\nExample Results:")
    print(df[["problem_id", "success", "execution_success"]].to_string(index=False))


if __name__ == "__main__":
    main()

