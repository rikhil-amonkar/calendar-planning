import os
import json
import pandas as pd
from pathlib import Path
import logging

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)

def analyze_task_results(task, model, output_dir="../output/SMT"):
    """Analyze results for a specific task and model"""
    task_dir = os.path.join(output_dir, model, task, "n_pass")
    if not os.path.exists(task_dir):
        logging.warning(f"Directory not found: {task_dir}")
        return None, None
    
    # Lists to store data for both sheets
    summary_data = []
    detailed_data = []
    
    # Walk through all example directories
    for example_dir in os.listdir(task_dir):
        example_path = os.path.join(task_dir, example_dir)
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
    # Define tasks and models to analyze
    tasks = ["calendar", "trip", "meeting"]
    models = ["DeepSeek-R1"]  # Add more models if needed
    
    # Create Excel writer
    output_file = "task_analysis_results.xlsx"
    with pd.ExcelWriter(output_file, engine='openpyxl') as writer:
        for task in tasks:
            for model in models:
                logging.info(f"Analyzing {task} results for {model}")
                
                # Get analysis results
                summary_df, detailed_df = analyze_task_results(task, model)
                
                if summary_df is not None and not summary_df.empty:
                    # Write summary sheet
                    sheet_name = f"{task}_{model}_summary"
                    summary_df.to_excel(writer, sheet_name=sheet_name, index=False)
                    
                    # Write detailed sheet
                    sheet_name = f"{task}_{model}_detailed"
                    detailed_df.to_excel(writer, sheet_name=sheet_name, index=False)
                    
                    logging.info(f"Wrote {len(summary_df)} examples to {sheet_name}")
                else:
                    logging.warning(f"No data found for {task} - {model}")
    
    logging.info(f"Analysis complete. Results written to {output_file}")

if __name__ == "__main__":
    main() 