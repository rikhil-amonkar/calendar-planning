"""
Analyze Results Script

This script analyzes the results of SMT/Python/Plan task execution and generates Excel reports.

Usage Examples:
    # Analyze calendar task results
    python3 analyze_results.py --task_dir ../output/SMT/meta-llama/Llama-3.1-8B-Instruct_20250619/calendar/n_pass
    
    # Analyze trip task results  
    python3 analyze_results.py --task_dir ../output/SMT/meta-llama/Llama-3.1-8B-Instruct_20250619/trip/n_pass
    
    # Analyze meeting task results
    python3 analyze_results.py --task_dir ../output/SMT/meta-llama/Llama-3.1-8B-Instruct_20250619/meeting/n_pass
    
    # Analyze results from different model (DeepSeek-R1)
    python3 analyze_results.py --task_dir ../output/SMT/DeepSeek-R1/calendar/n_pass
    
    # Analyze results from Python approach
    python3 analyze_results.py --task_dir ../output/Python/DeepSeek-R1/trip/n_pass

Output:
    - Excel file with summary and detailed sheets
    - File location: ../output/{approach}/{model_name}/task_analysis_results_{approach}_{model_name}_{task_name}.xlsx
"""

import os
import json
import pandas as pd
from pathlib import Path
import logging
import argparse

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)

def get_approach_from_path(model_path):
    """Extract approach (SMT, Python, Plan) from the path"""
    # If path is just the model name, try to find it in output directory
    if not os.path.dirname(model_path):
        # Look in output directory for the model
        output_dir = "../output"
        for approach in ['SMT', 'Python', 'Plan']:
            if os.path.exists(os.path.join(output_dir, approach, model_path)):
                return approach
        return 'Unknown'
    
    # Split path and look for approach in parent directories
    path_parts = Path(model_path).parts
    for part in reversed(path_parts):
        if part in ['SMT', 'Python', 'Plan']:
            return part
    return 'Unknown'

def analyze_task_results(task_dir_path, output_dir="../output"):
    """Analyze results for a specific task directory"""
    # Check if the provided path is a valid n_pass directory
    if not os.path.exists(task_dir_path):
        logging.warning(f"Directory not found: {task_dir_path}")
        return None, None
    
    # Extract model name and approach from path for output naming
    path_parts = Path(task_dir_path).parts
    model_name = "Unknown"
    approach = "Unknown"
    
    # Try to extract model name and approach from the path
    for i, part in enumerate(path_parts):
        if part in ['SMT', 'Python', 'Plan']:
            approach = part
            if i + 1 < len(path_parts):
                model_name = path_parts[i + 1]
            break
    
    # Lists to store data for both sheets
    summary_data = []
    detailed_data = []
    
    # Walk through all example directories
    for example_dir in os.listdir(task_dir_path):
        example_path = os.path.join(task_dir_path, example_dir)
        if not os.path.isdir(example_path):
            continue
            
        # Count number of passes (subdirectories)
        pass_dirs = [d for d in os.listdir(example_path) 
                    if os.path.isdir(os.path.join(example_path, d)) and d.endswith('_pass')]
        num_passes = len(pass_dirs)
        
        # Add to summary data
        summary_data.append({
            'Example Name': example_dir,
            'Number of Passes': num_passes
        })
        
        # Process each pass
        for pass_dir in sorted(pass_dirs, key=lambda x: int(x.split('_')[0])):
            eval_path = os.path.join(example_path, pass_dir, 'evaluation.json')
            if not os.path.exists(eval_path):
                logging.warning(f"Evaluation file not found: {eval_path}")
                continue
                
            try:
                with open(eval_path, 'r') as f:
                    eval_data = json.load(f)
                    
                # Extract relevant fields
                pass_data = {
                    'Example Name': example_dir,
                    'Pass Number': eval_data.get('pass_number', ''),
                    'Has Execution Error': eval_data.get('has_execution_error', False),
                    'Status': eval_data.get('status', ''),
                    'Is Exact Match': eval_data.get('is_exact_match', False),
                    'Constraints Satisfied': eval_data.get('constraints_satisfied', False),
                    'Execution Output': eval_data.get('execution_output', '')[:1000]  # Truncate long outputs
                }
                detailed_data.append(pass_data)
                
            except Exception as e:
                logging.error(f"Error processing {eval_path}: {str(e)}")
                continue
    
    # Create DataFrames
    summary_df = pd.DataFrame(summary_data)
    detailed_df = pd.DataFrame(detailed_data)
    
    return summary_df, detailed_df

def main():
    # Set up argument parser
    parser = argparse.ArgumentParser(description='Analyze task results')
    parser.add_argument('--task_dir', type=str, required=True,
                      help='Path to the task\'s n_pass folder (e.g., ../output/SMT/meta-llama/Llama-3.1-8B-Instruct_20250619/calendar/n_pass)')
    args = parser.parse_args()

    # Extract model name and approach from path for output naming
    path_parts = Path(args.task_dir).parts
    model_name = "Unknown"
    approach = "Unknown"
    task_name = "Unknown"
    
    # Try to extract model name, approach, and task from the path
    for i, part in enumerate(path_parts):
        if part in ['SMT', 'Python', 'Plan']:
            approach = part
            if i + 1 < len(path_parts):
                model_name = path_parts[i + 1]
            if i + 2 < len(path_parts):
                task_name = path_parts[i + 2]
            break
    
    # Create output directory path
    output_dir = "../output"
    excel_dir = os.path.join(output_dir, approach, model_name)
    os.makedirs(excel_dir, exist_ok=True)
    
    # Create Excel writer with approach in filename
    output_file = os.path.join(excel_dir, f"task_analysis_results_{approach}_{model_name}_{task_name}.xlsx")
    
    logging.info(f"Analyzing results for {task_name} from {args.task_dir}")
    
    # Get analysis results
    summary_df, detailed_df = analyze_task_results(args.task_dir)
    
    if summary_df is not None and not summary_df.empty:
        with pd.ExcelWriter(output_file, engine='openpyxl') as writer:
            # Write summary sheet
            sheet_name = f"{task_name}_{approach}_{model_name}_summary"
            summary_df.to_excel(writer, sheet_name=sheet_name, index=False)
            
            # Write detailed sheet
            sheet_name = f"{task_name}_{approach}_{model_name}_detailed"
            detailed_df.to_excel(writer, sheet_name=sheet_name, index=False)
            
            logging.info(f"Wrote {len(summary_df)} examples to {sheet_name}")
        logging.info(f"Analysis complete. Results written to {output_file}")
    else:
        logging.error("No data found. No Excel file was created.")

if __name__ == "__main__":
    main() 