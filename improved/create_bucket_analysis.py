import os
import json
import re
from collections import defaultdict
from pathlib import Path

def parse_bucket_summary(summary_file):
    """
    Parse the bucket summary file to create a mapping of example_id -> bucket
    """
    bucket_mapping = {}
    current_bucket = None
    
    with open(summary_file, 'r') as f:
        for line in f:
            line = line.strip()
            
            # Check if this is a bucket header
            if "80-100%" in line:
                current_bucket = "80-100%"
            elif "60-80%" in line:
                current_bucket = "60-80%"
            elif "40-60%" in line:
                current_bucket = "40-60%"
            elif "20-40%" in line:
                current_bucket = "20-40%"
            elif "0-20%" in line:
                current_bucket = "0-20%"
            
            # Parse example lines (format: "meeting_planning_example_XXX: Y constraints")
            if current_bucket and "meeting_planning_example_" in line and ":" in line:
                match = re.match(r"meeting_planning_example_(\d+):\s*\d+\s*constraints", line)
                if match:
                    example_id = f"meeting_planning_example_{match.group(1)}"
                    bucket_mapping[example_id] = current_bucket
    
    return bucket_mapping

def extract_run_info(filename):
    """
    Extract run information from filename
    Format: meeting_{method}_iterations_{model}_{timestamp}_structured_iterations_constraint_eval.json
    """
    # Remove extension
    base = filename.replace("_structured_iterations_constraint_eval.json", "")
    
    # Parse components
    parts = base.split("_")
    
    # Find method (python or smt)
    method = None
    if "python" in parts:
        method = "python"
    elif "smt" in parts:
        method = "smt"
    
    # Find model (everything between "iterations" and timestamp)
    model = None
    timestamp = None
    
    if "iterations" in parts:
        idx = parts.index("iterations")
        # Model is everything after "iterations" until we hit a date-like pattern
        model_parts = []
        for i in range(idx + 1, len(parts)):
            part = parts[i]
            # Check if this looks like a timestamp (starts with digits)
            if re.match(r'^\d{8}', part):
                timestamp = "_".join(parts[i:])
                break
            model_parts.append(part)
        
        if model_parts:
            model = "_".join(model_parts)
    
    return {
        "method": method,
        "model": model,
        "timestamp": timestamp,
        "filename": filename
    }

def process_final_json(final_json_path, bucket_mapping):
    """
    Process a final JSON file and create bucket analysis
    """
    with open(final_json_path, 'r') as f:
        data = json.load(f)
    
    # Extract run info from filename
    filename = os.path.basename(final_json_path)
    run_info = extract_run_info(filename)
    
    # Get summary stats
    summary = data.get("summary", {})
    results = data.get("results", [])
    
    # Create example-level data with bucket assignments
    examples = []
    bucket_stats = defaultdict(lambda: {"total": 0, "correct": 0, "examples": []})
    
    for result in results:
        problem_id = result.get("problem_id", "")
        bucket = bucket_mapping.get(problem_id, "unknown")
        is_correct = result.get("is_correct", False)
        
        example_data = {
            "problem_id": problem_id,
            "bucket": bucket,
            "is_correct": is_correct,
            "status": result.get("status", ""),
            "num_iterations": result.get("num_iterations", 0),
            "execution_success": result.get("execution_success", False)
        }
        examples.append(example_data)
        
        # Update bucket stats
        if bucket != "unknown":
            bucket_stats[bucket]["total"] += 1
            if is_correct:
                bucket_stats[bucket]["correct"] += 1
            bucket_stats[bucket]["examples"].append(example_data)
    
    # Calculate bucket accuracies
    bucket_accuracies = {}
    for bucket in ["80-100%", "60-80%", "40-60%", "20-40%", "0-20%"]:
        stats = bucket_stats[bucket]
        total = stats["total"]
        correct = stats["correct"]
        accuracy = correct / total if total > 0 else 0.0
        bucket_accuracies[bucket] = {
            "total": total,
            "correct": correct,
            "accuracy": accuracy,
            "accuracy_percentage": f"{accuracy * 100:.2f}%"
        }
    
    # Create output structure
    output = {
        "run_info": run_info,
        "summary": summary,
        "bucket_accuracies": bucket_accuracies,
        "examples": examples
    }
    
    return output

def create_markdown_summary(bucket_analyses, output_path):
    """
    Create a markdown file summarizing all bucket analyses
    """
    with open(output_path, 'w') as f:
        f.write("# Iterative Pass Results - Bucket Analysis\n\n")
        f.write("This document provides a comprehensive analysis of model performance across different constraint difficulty buckets.\n\n")
        
        # Overall summary table
        f.write("## Overall Summary\n\n")
        f.write("| Run | Method | Model | Overall Accuracy | Total | Correct |\n")
        f.write("|-----|--------|-------|------------------|-------|---------|\n")
        
        for analysis in bucket_analyses:
            run_info = analysis["run_info"]
            summary = analysis["summary"]
            method = run_info.get("method", "unknown")
            model = run_info.get("model", "unknown")
            accuracy = summary.get("accuracy", 0.0)
            total = summary.get("total", 0)
            correct = summary.get("correct", 0)
            
            f.write(f"| {run_info['filename']} | {method} | {model} | {accuracy*100:.2f}% | {total} | {correct} |\n")
        
        # Bucket-level analysis
        f.write("\n## Bucket-Level Performance\n\n")
        f.write("### Accuracy by Bucket\n\n")
        f.write("| Run | Method | Model | 80-100% | 60-80% | 40-60% | 20-40% | 0-20% |\n")
        f.write("|-----|--------|-------|---------|--------|--------|--------|-------|\n")
        
        for analysis in bucket_analyses:
            run_info = analysis["run_info"]
            bucket_accs = analysis["bucket_accuracies"]
            method = run_info.get("method", "unknown")
            model = run_info.get("model", "unknown")
            
            acc_80 = bucket_accs.get("80-100%", {}).get("accuracy_percentage", "N/A")
            acc_60 = bucket_accs.get("60-80%", {}).get("accuracy_percentage", "N/A")
            acc_40 = bucket_accs.get("40-60%", {}).get("accuracy_percentage", "N/A")
            acc_20 = bucket_accs.get("20-40%", {}).get("accuracy_percentage", "N/A")
            acc_0 = bucket_accs.get("0-20%", {}).get("accuracy_percentage", "N/A")
            
            f.write(f"| {run_info['filename']} | {method} | {model} | {acc_80} | {acc_60} | {acc_40} | {acc_20} | {acc_0} |\n")
        
        # Detailed bucket statistics
        f.write("\n### Detailed Bucket Statistics\n\n")
        
        for analysis in bucket_analyses:
            run_info = analysis["run_info"]
            bucket_accs = analysis["bucket_accuracies"]
            
            f.write(f"#### {run_info['filename']}\n\n")
            f.write("| Bucket | Total | Correct | Accuracy |\n")
            f.write("|--------|-------|---------|----------|\n")
            
            for bucket in ["80-100%", "60-80%", "40-60%", "20-40%", "0-20%"]:
                stats = bucket_accs.get(bucket, {})
                total = stats.get("total", 0)
                correct = stats.get("correct", 0)
                accuracy = stats.get("accuracy_percentage", "N/A")
                f.write(f"| {bucket} | {total} | {correct} | {accuracy} |\n")
            
            f.write("\n")

def main():
    # Paths
    base_dir = Path(__file__).parent
    final_dir = base_dir / "iterative_pass_results" / "final"
    buckets_dir = base_dir / "iterative_pass_results" / "buckets"
    bucket_summary = base_dir.parent / "output" / "Buckets" / "NEW_BUCKETS" / "constraint_summary_meeting.txt"
    
    # Create buckets directory
    buckets_dir.mkdir(parents=True, exist_ok=True)
    
    # Parse bucket mapping
    print("Parsing bucket summary...")
    bucket_mapping = parse_bucket_summary(bucket_summary)
    print(f"Found {len(bucket_mapping)} examples in buckets")
    
    # Process all final JSON files
    final_files = list(final_dir.glob("*.json"))
    print(f"Found {len(final_files)} final JSON files")
    
    bucket_analyses = []
    
    for final_file in final_files:
        print(f"Processing {final_file.name}...")
        
        # Process the file
        analysis = process_final_json(final_file, bucket_mapping)
        bucket_analyses.append(analysis)
        
        # Save individual analysis
        output_filename = final_file.stem.replace("_structured_iterations_constraint_eval", "_bucket_analysis") + ".json"
        output_path = buckets_dir / output_filename
        
        with open(output_path, 'w') as f:
            json.dump(analysis, f, indent=2)
        
        print(f"  Saved to {output_path}")
    
    # Create markdown summary
    markdown_path = buckets_dir / "bucket_analysis_summary.md"
    print(f"\nCreating markdown summary...")
    create_markdown_summary(bucket_analyses, markdown_path)
    print(f"Markdown summary saved to {markdown_path}")
    
    print("\nDone!")

if __name__ == "__main__":
    main()
