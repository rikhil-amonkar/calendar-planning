#!/usr/bin/env python3
"""
Generate bucketed evaluation results from standard evaluation JSON files.

This script:
1. Loads evaluation JSON files from the eval_results folder
2. Maps each example to its difficulty bucket (0-20%, 20-40%, 40-60%, 60-80%, 80-100%)
3. Creates new JSON files organized by buckets with bucket labels
4. Generates a final evaluation markdown file showing percentages by bucket
"""

import json
import re
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Tuple, Optional

# Paths
BUCKETS_BASE_DIR = Path(__file__).parent.parent.parent / "output" / "Buckets" / "bucketed_result_groups" / "meeting"
EVAL_RESULTS_DIR = Path(__file__).parent.parent / "eval_results"
OUTPUT_DIR = Path(__file__).parent

# Bucket folders
BUCKETS = ["0-20%", "20-40%", "40-60%", "60-80%", "80-100%"]


def build_bucket_mapping() -> Dict[str, str]:
    """
    Build a mapping from problem_id to bucket name.
    
    Returns:
        Dictionary mapping problem_id (e.g., "meeting_planning_example_115") to bucket (e.g., "0-20%")
    """
    bucket_mapping = {}
    
    for bucket in BUCKETS:
        bucket_dir = BUCKETS_BASE_DIR / bucket
        if not bucket_dir.exists():
            print(f"Warning: Bucket directory {bucket_dir} does not exist")
            continue
        
        # List all JSON files in this bucket
        for json_file in bucket_dir.glob("*.json"):
            # Extract problem_id from filename like "meeting_planning_example_115_output.json"
            match = re.match(r"meeting_planning_example_(\d+)_output\.json", json_file.name)
            if match:
                problem_id = f"meeting_planning_example_{match.group(1)}"
                bucket_mapping[problem_id] = bucket
            else:
                print(f"Warning: Could not parse filename {json_file.name}")
    
    return bucket_mapping


def parse_filename(filename: str) -> Tuple[Optional[str], Optional[str], Optional[str]]:
    """
    Parse evaluation filename to extract approach, model, and timestamp.
    
    Example: "meeting_python_deepseek-chat_20260117_052314_structured_iterations_constraint_eval.json"
    Returns: ("python", "deepseek-chat", "20260117_052314")
    """
    # Remove .json extension
    name = filename.replace(".json", "")
    
    # Pattern: meeting_{approach}_{model}_{timestamp}_structured_iterations_constraint_eval
    match = re.match(r"meeting_(\w+)_([^_]+)_(\d+_\d+)_structured_iterations_constraint_eval", name)
    if match:
        return match.group(1), match.group(2), match.group(3)
    
    return None, None, None


def load_eval_file(filepath: Path) -> Optional[Dict]:
    """Load an evaluation JSON file."""
    try:
        with open(filepath, 'r') as f:
            return json.load(f)
    except Exception as e:
        print(f"Error loading {filepath}: {e}")
        return None


def create_bucketed_result(eval_data: Dict, bucket_mapping: Dict[str, str], 
                          approach: str, model: str) -> Dict:
    """
    Create a bucketed result structure from evaluation data.
    
    Args:
        eval_data: The evaluation JSON data
        bucket_mapping: Mapping from problem_id to bucket
        approach: The approach used (e.g., "python", "smt")
        model: The model name (e.g., "deepseek-chat")
    
    Returns:
        Dictionary with bucketed results organized by bucket
    """
    # Initialize bucket structure
    bucketed = {
        "metadata": {
            "approach": approach,
            "model": model,
            "total_examples": eval_data["summary"]["total"]
        },
        "buckets": {
            "0-20%": [],
            "20-40%": [],
            "40-60%": [],
            "60-80%": [],
            "80-100%": []
        },
        "summary": {
            "0-20%": {"total": 0, "correct": 0, "accuracy": 0.0},
            "20-40%": {"total": 0, "correct": 0, "accuracy": 0.0},
            "40-60%": {"total": 0, "correct": 0, "accuracy": 0.0},
            "60-80%": {"total": 0, "correct": 0, "accuracy": 0.0},
            "80-100%": {"total": 0, "correct": 0, "accuracy": 0.0}
        }
    }
    
    # Process each result
    for result in eval_data.get("results", []):
        problem_id = result.get("problem_id", "")
        bucket = bucket_mapping.get(problem_id)
        
        if not bucket:
            print(f"Warning: No bucket found for problem_id {problem_id}")
            continue
        
        # Add bucket label to result
        result_with_bucket = result.copy()
        result_with_bucket["bucket"] = bucket
        
        # Add to appropriate bucket
        bucketed["buckets"][bucket].append(result_with_bucket)
        
        # Update summary
        bucketed["summary"][bucket]["total"] += 1
        if result.get("is_correct", False):
            bucketed["summary"][bucket]["correct"] += 1
    
    # Calculate accuracies
    for bucket in BUCKETS:
        summary = bucketed["summary"][bucket]
        if summary["total"] > 0:
            summary["accuracy"] = summary["correct"] / summary["total"]
        else:
            summary["accuracy"] = 0.0
    
    return bucketed


def generate_all_bucketed_results():
    """Process all evaluation JSON files and generate bucketed results."""
    print("Building bucket mapping...")
    bucket_mapping = build_bucket_mapping()
    print(f"Found {len(bucket_mapping)} examples mapped to buckets")
    
    # Find all evaluation JSON files
    eval_files = sorted(EVAL_RESULTS_DIR.glob("meeting_*_constraint_eval.json"))
    print(f"\nFound {len(eval_files)} evaluation files")
    
    all_bucketed_results = []
    
    for eval_file in eval_files:
        print(f"\nProcessing {eval_file.name}...")
        
        # Parse filename
        approach, model, timestamp = parse_filename(eval_file.name)
        if not approach or not model:
            print(f"  Warning: Could not parse filename, skipping")
            continue
        
        print(f"  Approach: {approach}, Model: {model}")
        
        # Load evaluation data
        eval_data = load_eval_file(eval_file)
        if not eval_data:
            continue
        
        # Create bucketed result
        bucketed = create_bucketed_result(eval_data, bucket_mapping, approach, model)
        
        # Save bucketed result
        output_filename = eval_file.name.replace("_constraint_eval.json", "_bucketed_results.json")
        output_path = OUTPUT_DIR / output_filename
        
        with open(output_path, 'w') as f:
            json.dump(bucketed, f, indent=2)
        
        print(f"  Saved bucketed results to {output_path}")
        all_bucketed_results.append({
            "file": output_filename,
            "approach": approach,
            "model": model,
            "data": bucketed
        })
    
    return all_bucketed_results


def generate_evaluation_markdown(all_bucketed_results: List[Dict]):
    """Generate final evaluation markdown file showing percentages by bucket."""
    
    # Group by approach and model
    results_by_key = {}
    for result in all_bucketed_results:
        key = (result["approach"], result["model"])
        if key not in results_by_key:
            results_by_key[key] = []
        results_by_key[key].append(result["data"])
    
    # Generate markdown
    md_lines = [
        "# Evaluation Results by Difficulty Bucket",
        "",
        "This report shows the accuracy percentages for each model and approach, ",
        "broken down by difficulty bucket (based on final answer correctness).",
        "",
        "## Summary",
        "",
        "| Model | Approach | 0-20% | 20-40% | 40-60% | 60-80% | 80-100% | Overall |",
        "|-------|----------|-------|--------|--------|--------|---------|---------|"
    ]
    
    # Sort by approach, then model
    sorted_keys = sorted(results_by_key.keys())
    
    for approach, model in sorted_keys:
        bucketed_data = results_by_key[(approach, model)][0]  # Take first if multiple
        summary = bucketed_data["summary"]
        
        # Calculate overall accuracy
        total_correct = sum(s["correct"] for s in summary.values())
        total_examples = sum(s["total"] for s in summary.values())
        overall_accuracy = (total_correct / total_examples * 100) if total_examples > 0 else 0.0
        
        # Format percentages
        acc_0_20 = summary["0-20%"]["accuracy"] * 100
        acc_20_40 = summary["20-40%"]["accuracy"] * 100
        acc_40_60 = summary["40-60%"]["accuracy"] * 100
        acc_60_80 = summary["60-80%"]["accuracy"] * 100
        acc_80_100 = summary["80-100%"]["accuracy"] * 100
        
        md_lines.append(
            f"| {model} | {approach.upper()} | "
            f"{acc_0_20:.1f}% | {acc_20_40:.1f}% | {acc_40_60:.1f}% | "
            f"{acc_60_80:.1f}% | {acc_80_100:.1f}% | {overall_accuracy:.1f}% |"
        )
    
    md_lines.extend([
        "",
        "## Detailed Statistics",
        ""
    ])
    
    for approach, model in sorted_keys:
        bucketed_data = results_by_key[(approach, model)][0]
        summary = bucketed_data["summary"]
        
        md_lines.extend([
            f"### {model} ({approach.upper()})",
            "",
            "| Bucket | Total | Correct | Accuracy |",
            "|--------|-------|---------|----------|"
        ])
        
        for bucket in BUCKETS:
            s = summary[bucket]
            md_lines.append(
                f"| {bucket} | {s['total']} | {s['correct']} | {s['accuracy']*100:.1f}% |"
            )
        
        md_lines.append("")
    
    # Write markdown file
    output_path = OUTPUT_DIR / "BUCKETED_EVALUATION_RESULTS.md"
    with open(output_path, 'w') as f:
        f.write("\n".join(md_lines))
    
    print(f"\n✓ Generated evaluation markdown: {output_path}")
    return output_path


if __name__ == "__main__":
    print("=" * 60)
    print("Generating Bucketed Evaluation Results")
    print("=" * 60)
    
    # Generate all bucketed results
    all_bucketed_results = generate_all_bucketed_results()
    
    # Generate final evaluation markdown
    if all_bucketed_results:
        generate_evaluation_markdown(all_bucketed_results)
        print(f"\n✓ Processed {len(all_bucketed_results)} evaluation files")
    else:
        print("\n✗ No evaluation files processed")
