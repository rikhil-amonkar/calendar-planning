#!/usr/bin/env python3
"""
LLM-as-a-Judge Evaluation Script
Uses GPT-5.2 (or other model) to evaluate if generated solutions are correct.
"""

import os
import json
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from datetime import datetime
from openai import OpenAI
from dotenv import load_dotenv
import pandas as pd
from tqdm import tqdm

load_dotenv()


class LLMJudgeEvaluator:
    """Use an LLM to judge if solutions are correct."""
    
    def __init__(self, 
                 judge_model: str = "gpt-5.2",
                 results_file: str = None,
                 temperature: float = 0.3,
                 delay: float = 1.0):
        """
        Initialize LLM judge evaluator.
        
        Args:
            judge_model: Model to use as judge (e.g., gpt-5.2, deepseek-v3)
            results_file: Path to results JSON file
            temperature: Temperature for judge (lower = more consistent)
            delay: Delay between API calls to avoid rate limits
        """
        # Initialize appropriate API client based on model
        if judge_model.startswith("deepseek-"):
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
        
        self.judge_model = judge_model
        self.temperature = temperature
        self.delay = delay
        
        if results_file:
            self.results_file = Path(results_file)
            self.results = self._load_results()
        else:
            self.results = None
    
    def _load_results(self) -> List[Dict]:
        """Load results from JSON file."""
        with open(self.results_file, 'r') as f:
            data = json.load(f)
        print(f"✓ Loaded {len(data)} results from {self.results_file}")
        return data
    
    def create_judge_prompt(self, 
                           problem_text: str, 
                           model_output: str, 
                           golden_solution: str,
                           include_golden: bool = True) -> str:
        """
        Create a prompt for the judge to evaluate the solution.
        
        Args:
            problem_text: The original problem
            model_output: The model's solution
            golden_solution: The reference solution
            include_golden: Whether to show golden solution to judge
        
        Returns:
            Evaluation prompt
        """
        if include_golden:
            prompt = f"""You are an expert evaluator for planning and scheduling problems.

Your task: Determine if the MODEL SOLUTION correctly solves the given problem.

A solution is CORRECT if:
1. It satisfies all constraints (time windows, durations, travel times)
2. It achieves the stated objective (e.g., meet required people)
3. The logic and calculations are sound
4. Time formatting is valid and consistent (no mixed formats like "21:45PM" - times should be either 12-hour format with AM/PM like "9:45PM" OR 24-hour format without AM/PM like "21:45", never mixed)

A solution can be correct even if it differs from the reference solution (e.g., different wait strategies, meeting durations beyond minimum).

PROBLEM:
{problem_text}

MODEL SOLUTION:
{model_output}

REFERENCE SOLUTION (for comparison, but model doesn't have to match exactly):
{golden_solution}

EVALUATION INSTRUCTIONS:
1. Check if the model solution satisfies all problem constraints
2. Verify times, durations, and feasibility
3. Check for formatting errors (e.g., "21:45PM" is INVALID - mixing 24-hour format with AM/PM)
4. Compare key outcomes (who is met, when, for how long)
5. Determine if it's correct even if approach differs from reference

Respond in this exact format:
VERDICT: [CORRECT or INCORRECT]
REASONING: [1-2 sentence explanation]
KEY_ISSUES: [list any constraint violations or formatting errors, or "none" if correct]"""
        else:
            prompt = f"""You are an expert evaluator for planning and scheduling problems.

Your task: Determine if the given SOLUTION correctly solves the PROBLEM.

A solution is CORRECT if:
1. It satisfies all constraints (time windows, durations, travel times)
2. It achieves the stated objective
3. The logic and calculations are sound
4. Time formatting is valid and consistent (no mixed formats like "21:45PM" - times should be either 12-hour format with AM/PM like "9:45PM" OR 24-hour format without AM/PM like "21:45", never mixed)

PROBLEM:
{problem_text}

SOLUTION:
{model_output}

EVALUATION INSTRUCTIONS:
1. Check if the solution satisfies all problem constraints
2. Verify times, durations, and feasibility
3. Check for formatting errors (e.g., "21:45PM" is INVALID - mixing 24-hour format with AM/PM)
4. Determine if the solution correctly solves the problem

Respond in this exact format:
VERDICT: [CORRECT or INCORRECT]
REASONING: [1-2 sentence explanation]
KEY_ISSUES: [list any constraint violations or formatting errors, or "none" if correct]"""
        
        return prompt
    
    def parse_judge_response(self, response: str) -> Dict:
        """
        Parse the judge's response into structured format.
        
        Args:
            response: Raw response from judge
        
        Returns:
            Dictionary with verdict, reasoning, and issues
        """
        import re
        
        verdict_match = re.search(r'VERDICT:\s*(CORRECT|INCORRECT)', response, re.IGNORECASE)
        verdict = verdict_match.group(1).upper() if verdict_match else "UNKNOWN"
        
        reasoning_match = re.search(r'REASONING:\s*(.+?)(?=KEY_ISSUES:|$)', response, re.DOTALL | re.IGNORECASE)
        reasoning = reasoning_match.group(1).strip() if reasoning_match else ""
        
        issues_match = re.search(r'KEY_ISSUES:\s*(.+?)$', response, re.DOTALL | re.IGNORECASE)
        issues = issues_match.group(1).strip() if issues_match else ""
        
        return {
            'verdict': verdict,
            'reasoning': reasoning,
            'key_issues': issues,
            'raw_response': response
        }
    
    def judge_single_result(self, 
                           result: Dict,
                           include_golden: bool = True) -> Dict:
        """
        Have LLM judge a single result.
        
        Args:
            result: Result dictionary with problem, output, golden solution
            include_golden: Whether to show golden solution to judge
        
        Returns:
            Judgment dictionary
        """
        problem_text = result.get('model_response', '')
        
        # Extract just the problem from model_response if it contains the full prompt
        # Try to find the original problem text
        if 'TASK:' in problem_text or 'CONSTRAINTS:' in problem_text:
            # It's likely the full prompt, try to extract problem
            problem_text = problem_text
        
        model_output = result.get('output', '')
        golden_solution = result.get('golden_solution', '')
        
        # Skip if no output (execution failed)
        if not model_output:
            return {
                'verdict': 'INCORRECT',
                'reasoning': 'Code execution failed - no output produced',
                'key_issues': 'Execution failure',
                'raw_response': '',
                'judge_error': None
            }
        
        # Create judge prompt
        prompt = self.create_judge_prompt(
            problem_text, 
            model_output, 
            golden_solution,
            include_golden=include_golden
        )
        
        # Get judgment from LLM
        try:
            api_params = {
                "model": self.judge_model,
                "messages": [{"role": "user", "content": prompt}],
                "temperature": self.temperature
            }
            
            # Don't add temperature for reasoning models (O1, O3, GPT-5, Deepseek-Reasoner)
            reasoning_models = ["o1", "o3", "gpt-5", "deepseek-reasoner"]
            if any(self.judge_model.lower().startswith(prefix) for prefix in reasoning_models):
                api_params.pop("temperature")
            
            response = self.client.chat.completions.create(**api_params)
            judge_response = response.choices[0].message.content
            
            # Parse response
            judgment = self.parse_judge_response(judge_response)
            judgment['judge_error'] = None
            
            return judgment
            
        except Exception as e:
            return {
                'verdict': 'ERROR',
                'reasoning': f'Judge API error: {str(e)}',
                'key_issues': 'API failure',
                'raw_response': '',
                'judge_error': str(e)
            }
    
    def evaluate_all(self, 
                     include_golden: bool = True,
                     max_samples: Optional[int] = None) -> pd.DataFrame:
        """
        Evaluate all results using LLM judge.
        
        Args:
            include_golden: Whether to show golden solutions to judge
            max_samples: Maximum number to evaluate (for testing)
        
        Returns:
            DataFrame with judgments
        """
        if not self.results:
            raise ValueError("No results loaded. Provide results_file when initializing.")
        
        results_to_eval = self.results[:max_samples] if max_samples else self.results
        
        print(f"\n{'='*70}")
        print(f"LLM Judge Evaluation")
        print(f"{'='*70}")
        print(f"Judge model: {self.judge_model}")
        print(f"Problems: {len(results_to_eval)}")
        print(f"Include golden: {include_golden}")
        print(f"{'='*70}\n")
        
        evaluations = []
        
        for result in tqdm(results_to_eval, desc="Judging results"):
            judgment = self.judge_single_result(result, include_golden=include_golden)
            
            evaluations.append({
                'problem_id': result.get('problem_id'),
                'problem_index': result.get('problem_index'),
                'task_type': result.get('task_type'),
                'execution_success': result.get('execution_success', False),
                'judge_verdict': judgment['verdict'],
                'judge_reasoning': judgment['reasoning'],
                'judge_issues': judgment['key_issues'],
                'judge_error': judgment['judge_error'],
                'output': result.get('output', ''),
                'golden_solution': result.get('golden_solution', ''),
                'model': result.get('model', ''),
            })
            
            # Delay to avoid rate limits
            time.sleep(self.delay)
        
        df = pd.DataFrame(evaluations)
        return df
    
    def print_summary(self, df: pd.DataFrame):
        """Print evaluation summary."""
        total = len(df)
        exec_success = df['execution_success'].sum()
        
        # Count verdicts
        correct = (df['judge_verdict'] == 'CORRECT').sum()
        incorrect = (df['judge_verdict'] == 'INCORRECT').sum()
        errors = (df['judge_verdict'] == 'ERROR').sum()
        unknown = (df['judge_verdict'] == 'UNKNOWN').sum()
        
        print(f"\n{'='*70}")
        print(f"JUDGE EVALUATION SUMMARY")
        print(f"{'='*70}")
        print(f"Total problems:          {total}")
        print(f"Code executed:           {exec_success} / {total} ({exec_success/total*100:.1f}%)")
        print(f"\nJudge Verdicts:")
        print(f"  CORRECT:               {correct} / {total} ({correct/total*100:.1f}%)")
        print(f"  INCORRECT:             {incorrect} / {total} ({incorrect/total*100:.1f}%)")
        print(f"  ERROR:                 {errors} / {total}")
        print(f"  UNKNOWN:               {unknown} / {total}")
        print(f"\nAccuracy (of executed): {correct} / {exec_success} ({correct/exec_success*100:.1f}%)" if exec_success > 0 else "")
        print(f"{'='*70}\n")
    
    def show_samples(self, df: pd.DataFrame, n: int = 5):
        """Show sample judgments."""
        print(f"\n{'='*70}")
        print(f"SAMPLE INCORRECT JUDGMENTS")
        print(f"{'='*70}\n")
        
        incorrect = df[df['judge_verdict'] == 'INCORRECT'].head(n)
        
        for idx, row in incorrect.iterrows():
            print(f"Problem: {row['problem_id']}")
            print(f"Verdict: {row['judge_verdict']}")
            print(f"Reasoning: {row['judge_reasoning'][:150]}")
            print(f"Issues: {row['judge_issues'][:150]}")
            print("-" * 70 + "\n")
        
        print(f"\n{'='*70}")
        print(f"SAMPLE CORRECT JUDGMENTS")
        print(f"{'='*70}\n")
        
        correct = df[df['judge_verdict'] == 'CORRECT'].head(n)
        
        for idx, row in correct.iterrows():
            print(f"✓ Problem: {row['problem_id']}")
            print(f"  Reasoning: {row['judge_reasoning'][:150]}")
            print()
    
    def save_evaluation(self, df: pd.DataFrame, output_name: str):
        """Save evaluation results."""
        output_dir = self.results_file.parent if self.results_file else Path(".")
        
        # Save CSV
        csv_path = output_dir / f"{output_name}_judge_eval.csv"
        df.to_csv(csv_path, index=False)
        print(f"✓ Judge evaluation saved to: {csv_path}")
        
        # Save detailed JSON
        json_path = output_dir / f"{output_name}_judge_eval.json"
        df.to_json(json_path, orient='records', indent=2)
        print(f"✓ Detailed evaluation saved to: {json_path}")


def main():
    """Main evaluation function."""
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python llm_judge_evaluator.py <results_file.json> [judge_model] [max_samples]")
        print("\nArguments:")
        print("  results_file  : Path to inference results JSON")
        print("  judge_model   : Model to use as judge (default: gpt-5.2)")
        print("  max_samples   : Max problems to evaluate (default: all)")
        print("\nExample:")
        print("  python llm_judge_evaluator.py code_generation_results/meeting_test_run.json gpt-5.2")
        print("  python llm_judge_evaluator.py results.json gpt-4 10")
        sys.exit(1)
    
    results_file = sys.argv[1]
    judge_model = sys.argv[2] if len(sys.argv) > 2 else "gpt-5.2"
    max_samples = int(sys.argv[3]) if len(sys.argv) > 3 else None
    
    if not Path(results_file).exists():
        print(f"Error: File not found: {results_file}")
        sys.exit(1)
    
    # Initialize evaluator
    evaluator = LLMJudgeEvaluator(
        judge_model=judge_model,
        results_file=results_file,
        temperature=0.3,
        delay=1.0  # 1 second between calls
    )
    
    # Run evaluation
    df = evaluator.evaluate_all(
        include_golden=True,  # Show golden solution for reference
        max_samples=max_samples
    )
    
    # Print summary
    evaluator.print_summary(df)
    
    # Show samples
    evaluator.show_samples(df, n=3)
    
    # Save results
    base_name = Path(results_file).stem
    evaluator.save_evaluation(df, f"{base_name}_{judge_model.replace('.', '_')}")
    
    print("\n" + "="*70)
    print("EVALUATION COMPLETE")
    print("="*70)
    print(f"Judge model: {judge_model}")
    print(f"Total evaluated: {len(df)}")
    print(f"Accuracy: {(df['judge_verdict'] == 'CORRECT').sum()}/{len(df)}")
    print("="*70 + "\n")


if __name__ == "__main__":
    main()

