#!/usr/bin/env python3
"""
Local model inference script for Natural Plan problems.
Uses local Qwen models to generate code, then executes it.
"""

import os
import re
import json
import subprocess
import tempfile
import torch
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from datetime import datetime
import pandas as pd
from tqdm import tqdm
from transformers import AutoTokenizer, AutoModelForCausalLM

from dataset_loader import NaturalPlanDataset, TaskType


class LocalModelInference:
    """Run code generation inference on Natural Plan problems using local models."""
    
    def __init__(self, 
                 model_name: str = "Qwen/Qwen2.5-32B-Instruct",
                 model_cache_dir: str = "/local-ssd/cek99/hf/transformers/",
                 prompt_strategy_file: str = "prompt_strategy.txt",
                 timeout: int = 30,
                 max_new_tokens: int = 4096,
                 temperature: float = 0.7):
        """
        Initialize the local model inference system.
        
        Args:
            model_name: HuggingFace model name (e.g., "Qwen/Qwen2.5-32B-Instruct")
            model_cache_dir: Directory where models are cached
            prompt_strategy_file: Path to file containing prompting strategy
            timeout: Timeout for code execution in seconds
            max_new_tokens: Maximum tokens to generate
            temperature: Sampling temperature
        """
        self.model_name = model_name
        self.model_cache_dir = model_cache_dir
        self.prompt_strategy_file = prompt_strategy_file
        self.timeout = timeout
        self.max_new_tokens = max_new_tokens
        self.temperature = temperature
        self.dataset = NaturalPlanDataset()
        
        print(f"Loading model: {model_name}")
        print(f"Cache directory: {model_cache_dir}")
        
        # Load model and tokenizer
        self.tokenizer = AutoTokenizer.from_pretrained(
            model_name,
            cache_dir=model_cache_dir,
            trust_remote_code=True
        )
        
        self.model = AutoModelForCausalLM.from_pretrained(
            model_name,
            cache_dir=model_cache_dir,
            torch_dtype=torch.bfloat16,
            device_map="auto",
            trust_remote_code=True
        )
        
        print(f"✓ Model loaded successfully\n")
        
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
        # Look for ```python ... ``` blocks
        pattern = r'```python\s*(.*?)```'
        matches = re.findall(pattern, response, re.DOTALL)
        
        if matches:
            # Return the last code block found
            return matches[-1].strip()
        
        # Also try without 'python' keyword
        pattern = r'```\s*(.*?)```'
        matches = re.findall(pattern, response, re.DOTALL)
        
        if matches:
            # Filter to find blocks that look like Python code
            for match in reversed(matches):
                code = match.strip()
                # Simple heuristic: contains Python keywords
                if any(keyword in code for keyword in ['def ', 'import ', 'print(', 'return ', '=']):
                    return code
        
        return None
    
    def execute_code(self, code: str) -> Tuple[bool, Optional[str]]:
        """
        Execute Python code in a temporary file and capture output.
        
        Args:
            code: Python code to execute
        
        Returns:
            Tuple of (success, output)
        """
        try:
            # Create a temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
                f.write(code)
                temp_file = f.name
            
            # Execute the code
            result = subprocess.run(
                ['python', temp_file],
                capture_output=True,
                text=True,
                timeout=self.timeout
            )
            
            # Clean up
            os.unlink(temp_file)
            
            if result.returncode == 0:
                return True, result.stdout.strip()
            else:
                return False, result.stderr.strip()
                
        except subprocess.TimeoutExpired:
            os.unlink(temp_file)
            return False, f"Execution timeout ({self.timeout}s)"
        except Exception as e:
            if 'temp_file' in locals():
                try:
                    os.unlink(temp_file)
                except:
                    pass
            return False, f"Execution error: {str(e)}"
    
    def generate_response(self, prompt: str) -> str:
        """
        Generate response from local model.
        
        Args:
            prompt: Input prompt
        
        Returns:
            Generated text
        """
        # Format prompt for chat models
        messages = [{"role": "user", "content": prompt}]
        
        # Apply chat template
        text = self.tokenizer.apply_chat_template(
            messages,
            tokenize=False,
            add_generation_prompt=True
        )
        
        # Tokenize
        inputs = self.tokenizer([text], return_tensors="pt").to(self.model.device)
        
        # Generate
        with torch.no_grad():
            outputs = self.model.generate(
                **inputs,
                max_new_tokens=self.max_new_tokens,
                temperature=self.temperature,
                do_sample=True if self.temperature > 0 else False,
                top_p=0.9,
                pad_token_id=self.tokenizer.eos_token_id
            )
        
        # Decode
        response = self.tokenizer.decode(
            outputs[0][len(inputs.input_ids[0]):],
            skip_special_tokens=True
        )
        
        return response
    
    def run_single_inference(self, 
                            task_type: TaskType, 
                            problem_index: int, 
                            split: str = "test",
                            shot_type: str = "0shot") -> Dict:
        """
        Run inference on a single problem.
        
        Args:
            task_type: Type of task
            problem_index: Index of the problem
            split: Data split to use
            shot_type: "0shot" or "5shot"
        
        Returns:
            Dictionary with results
        """
        # Load problem
        problem = self.dataset.get_problem(task_type, problem_index, split)
        
        # Format problem text with shot_type
        problem_text = self.dataset.format_problem(problem, shot_type)
        
        # Create full prompt
        full_prompt = self.create_prompt(problem_text)
        
        # Get model response
        try:
            model_response = self.generate_response(full_prompt)
            
        except Exception as e:
            return {
                "task_type": task_type,
                "problem_index": problem_index,
                "problem_id": problem.get("id"),
                "success": False,
                "error": f"Model generation error: {str(e)}",
                "model_response": None,
                "code": None,
                "execution_success": False,
                "output": None,
                "golden_solution": self.dataset.get_golden_solution(problem)
            }
        
        # Extract code
        code = self.extract_code(model_response)
        
        if not code:
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
                "golden_solution": self.dataset.get_golden_solution(problem)
            }
        
        # Execute code
        exec_success, output = self.execute_code(code)
        
        return {
            "task_type": task_type.value if hasattr(task_type, 'value') else task_type,
            "problem_index": problem_index,
            "problem_id": problem.get("id"),
            "success": True,
            "error": None,
            "model_response": model_response,
            "code": code,
            "execution_success": exec_success,
            "output": output,
            "golden_solution": self.dataset.get_golden_solution(problem)
        }
    
    def run_batch_inference(self,
                           task_type: TaskType,
                           problem_indices: List[int],
                           split: str = "test",
                           shot_type: str = "0shot") -> List[Dict]:
        """
        Run inference on multiple problems.
        
        Args:
            task_type: Type of task
            problem_indices: List of problem indices
            split: Data split to use
            shot_type: "0shot" or "5shot"
        
        Returns:
            List of result dictionaries
        """
        results = []
        
        print(f"\n{'='*70}")
        print(f"Code Generation Inference")
        print(f"{'='*70}")
        print(f"Model: {self.model_name}")
        print(f"Task: {task_type}")
        print(f"Problems: {len(problem_indices)}")
        print(f"Shot type: {shot_type}")
        print(f"Strategy: {self.prompt_strategy_file}")
        print(f"{'='*70}\n")
        
        for idx in tqdm(problem_indices, desc="Running inference"):
            result = self.run_single_inference(task_type, idx, split, shot_type)
            results.append(result)
        
        return results
    
    def save_results(self, results: List[Dict], task_type: str, model_name_short: str):
        """Save results to JSON and CSV files."""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_dir = Path("code_generation_results")
        output_dir.mkdir(exist_ok=True)
        
        # Create safe model name for filename
        safe_model_name = model_name_short.replace("/", "-").replace(".", "_")
        base_filename = f"{task_type}_test_{safe_model_name}_{timestamp}"
        
        # Save detailed JSON
        json_path = output_dir / f"{base_filename}.json"
        with open(json_path, 'w') as f:
            json.dump(results, f, indent=2)
        
        # Save CSV summary
        df = pd.DataFrame(results)
        csv_path = output_dir / f"{base_filename}.csv"
        df.to_csv(csv_path, index=False)
        
        # Print summary
        total = len(results)
        api_success = sum(1 for r in results if r.get('success', False))
        code_extracted = sum(1 for r in results if r.get('code') is not None)
        code_executed = sum(1 for r in results if r.get('execution_success', False))
        
        print(f"\n{'='*70}")
        print(f"SUMMARY")
        print(f"{'='*70}")
        print(f"Total problems: {total}")
        print(f"Generation success: {api_success} / {total}")
        print(f"Code extracted: {code_extracted} / {total}")
        print(f"Code executed: {code_executed} / {total}")
        print(f"{'='*70}\n")
        
        print(f"✓ Results saved to: {csv_path}")
        print(f"✓ Detailed results saved to: {json_path}\n")
        
        # Show example results
        print("Example Results:")
        sample_df = df[['problem_id', 'success', 'execution_success']].head(100)
        print(sample_df.to_string(index=False))


def main():
    """Main inference function."""
    import sys
    
    if len(sys.argv) < 4:
        print("Usage: python local_model_inference.py <model_name> <strategy_file> <task_type> [num_problems]")
        print("\nArguments:")
        print("  model_name     : HuggingFace model name")
        print("                   - Qwen/Qwen2.5-32B-Instruct")
        print("                   - Qwen/Qwen3-32B")
        print("  strategy_file  : Path to prompting strategy file")
        print("  task_type      : meeting, calendar, or trip")
        print("  num_problems   : Number of problems to run (default: 100)")
        print("\nExample:")
        print("  python local_model_inference.py Qwen/Qwen2.5-32B-Instruct strategies/my_strategy3.txt meeting 100")
        sys.exit(1)
    
    model_name = sys.argv[1]
    strategy_file = sys.argv[2]
    task_type_str = sys.argv[3]
    num_problems = int(sys.argv[4]) if len(sys.argv) > 4 else 100
    
    # Validate task type
    valid_task_types = ["meeting", "calendar", "trip"]
    
    if task_type_str not in valid_task_types:
        print(f"Error: Invalid task type '{task_type_str}'. Must be: meeting, calendar, or trip")
        sys.exit(1)
    
    task_type = task_type_str
    
    # Initialize inference
    print(f"\n{'='*70}")
    print(f"Code Generation Inference - Test Split")
    print(f"{'='*70}")
    print(f"Task: {task_type_str}")
    print(f"Problems: {num_problems}")
    print(f"{'='*70}\n")
    
    inference = LocalModelInference(
        model_name=model_name,
        model_cache_dir="/local-ssd/cek99/hf/transformers/",
        prompt_strategy_file=strategy_file,
        timeout=30,
        max_new_tokens=4096,
        temperature=0.7
    )
    
    # Run inference on test split
    problem_indices = list(range(num_problems))
    results = inference.run_batch_inference(
        task_type=task_type,
        problem_indices=problem_indices,
        split="test",
        shot_type="0shot"
    )
    
    # Save results
    model_short = model_name.split("/")[-1] if "/" in model_name else model_name
    inference.save_results(results, task_type_str, model_short)


if __name__ == "__main__":
    main()

