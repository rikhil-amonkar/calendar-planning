#!/usr/bin/env python3
"""
Compare LLM-judge and constraint-based evaluations across all models.
"""

import json
from pathlib import Path
from typing import Dict, Tuple


def get_evaluation_stats(file_path: str) -> Tuple[int, int, float]:
    """Get evaluation statistics from a file."""
    try:
        with open(file_path, 'r') as f:
            data = json.load(f)
        
        if 'summary' in data:
            # Constraint-based evaluation format
            return (
                data['summary']['correct'],
                data['summary']['total'],
                data['summary']['accuracy'] * 100
            )
        elif isinstance(data, list):
            # LLM judge evaluation format
            correct = sum(1 for item in data if item.get('judge_verdict') == 'CORRECT')
            total = len(data)
            return (correct, total, correct / total * 100 if total > 0 else 0)
        else:
            return (0, 0, 0)
    except:
        return (0, 0, 0)


def main():
    """Generate comparison report."""
    
    results_dir = Path("code_generation_results")
    
    # Define models and their file patterns
    models = {
        "GPT-5-Python": "meeting_test_gpt-5_20251224_021226",
        "GPT-5-SMT": "meeting_test_gpt-5-SMT_20260112_193420",
        "GPT-4o-mini": "meeting_test_gpt-4o-mini_20251231_182108",
        "O3-mini-Python": "meeting_test_o3-mini_20251231_201401",
        "O3-mini-SMT": "meeting_test_o3-mini-SMT_20260112_152624",
        "Deepseek-Reasoner-Python": "meeting_test_deepseek-reasoner-Python_20251231_224847",
        "Deepseek-Reasoner-SMT": "meeting_test_deepseek-reasoner-SMT_20260111_170345",
        "Deepseek-Chat-Python": "meeting_test_deepseek-chat_20260101_062046",
        "Deepseek-Chat-SMT": "meeting_test_deepseek-chat-SMT_20260112_153641",
        "Qwen2.5-32B-Python": "meeting_test_Qwen2_5-32B-Instruct_20260102_133432",
        "Qwen2.5-32B-SMT": "meeting_test_Qwen2_5-32B-Instruct-SMT_20260113_040825",
        "Qwen3-32B-Python": "meeting_test_Qwen3-32B_20260105_082658",
        "Qwen3-32B-SMT": "meeting_test_Qwen3-32B-SMT_20260112_041646"
        #"GPT-4o (test_run)": "meeting_test_run"
    }
    
    print("="*100)
    print("COMPREHENSIVE EVALUATION COMPARISON: LLM-Judge vs Constraint-Based")
    print("="*100)
    print()
    print(f"{'Model':<25} {'LLM Judge (GPT-5.2)':<30} {'Constraint-Based':<30} {'Difference':<15}")
    print(f"{'':25} {'Correct/Total':<15} {'Accuracy':<15} {'Correct/Total':<15} {'Accuracy':<15} {'(Δ%)':<15}")
    print("-"*100)
    
    results_summary = []
    
    for model_name, file_pattern in models.items():
        # LLM judge file
        judge_file = results_dir / f"{file_pattern}_gpt-5_2_judge_eval.json"
        judge_correct, judge_total, judge_acc = get_evaluation_stats(judge_file)
        
        # Constraint-based file
        constraint_file = results_dir / f"{file_pattern}_structured_constraint_eval.json"
        const_correct, const_total, const_acc = get_evaluation_stats(constraint_file)
        
        # Calculate difference
        diff = const_acc - judge_acc if judge_total > 0 and const_total > 0 else 0
        diff_str = f"{diff:+.1f}%" if judge_total > 0 and const_total > 0 else "N/A"
        
        # Format output
        judge_str = f"{judge_correct}/{judge_total}" if judge_total > 0 else "N/A"
        judge_acc_str = f"{judge_acc:.1f}%" if judge_total > 0 else "N/A"
        const_str = f"{const_correct}/{const_total}" if const_total > 0 else "N/A"
        const_acc_str = f"{const_acc:.1f}%" if const_total > 0 else "N/A"
        
        print(f"{model_name:<25} {judge_str:<15} {judge_acc_str:<15} {const_str:<15} {const_acc_str:<15} {diff_str:<15}")
        
        results_summary.append({
            'model': model_name,
            'llm_judge': {'correct': judge_correct, 'total': judge_total, 'accuracy': judge_acc},
            'constraint_based': {'correct': const_correct, 'total': const_total, 'accuracy': const_acc},
            'difference': diff
        })
    
    print("="*100)
    print()
    
    # Summary statistics
    print("KEY INSIGHTS:")
    print("-"*100)
    
    # Best performers
    if results_summary:
        # Sort by constraint-based accuracy (only models with data)
        sorted_constraint = sorted(
            [r for r in results_summary if r['constraint_based']['total'] > 0],
            key=lambda x: x['constraint_based']['accuracy'],
            reverse=True
        )
        
        if sorted_constraint:
            print(f"\n🏆 Top 3 Models (Constraint-Based Accuracy):")
            for i, model in enumerate(sorted_constraint[:3], 1):
                print(f"   {i}. {model['model']:<25} {model['constraint_based']['correct']}/{model['constraint_based']['total']} ({model['constraint_based']['accuracy']:.1f}%)")
        
        # Sort by LLM judge accuracy
        sorted_judge = sorted(
            [r for r in results_summary if r['llm_judge']['total'] > 0],
            key=lambda x: x['llm_judge']['accuracy'],
            reverse=True
        )
        
        if sorted_judge:
            print(f"\n🏆 Top 3 Models (LLM Judge Accuracy):")
            for i, model in enumerate(sorted_judge[:3], 1):
                print(f"   {i}. {model['model']:<25} {model['llm_judge']['correct']}/{model['llm_judge']['total']} ({model['llm_judge']['accuracy']:.1f}%)")
        
        # Models with largest differences
        valid_models = [r for r in results_summary if r['llm_judge']['total'] > 0 and r['constraint_based']['total'] > 0]
        if valid_models:
            sorted_diff = sorted(valid_models, key=lambda x: abs(x['difference']), reverse=True)
            print(f"\n📊 Largest Judge vs Constraint Differences:")
            for i, model in enumerate(sorted_diff[:3], 1):
                print(f"   {i}. {model['model']:<25} {model['difference']:+.1f}% (Judge: {model['llm_judge']['accuracy']:.1f}%, Constraint: {model['constraint_based']['accuracy']:.1f}%)")
    
    print()
    print("="*100)
    print()
    
    # Notes
    print("NOTES:")
    print("  • Both evaluations now count all 100 problems for fair comparison")
    print("  • LLM Judge is stricter: catches formatting errors, logical inconsistencies")
    print("  • Constraint-Based checks feasibility: time windows, travel times, meeting durations")
    print("  • Problems with no extractable plan or execution failures are counted as incorrect")
    print()


if __name__ == "__main__":
    main()
