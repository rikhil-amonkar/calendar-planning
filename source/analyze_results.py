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

def analyze_task_results(task, model_path, output_dir="../output"):
    """Analyze results for a specific task and model"""
    # Extract model name and approach from path
    model_name = os.path.basename(model_path)
    approach = get_approach_from_path(model_path)
    
    # Construct task directory path
    if approach == 'Unknown':
        # Try to find the model in each approach directory
        for possible_approach in ['SMT', 'Python', 'Plan']:
            task_dir = os.path.join(output_dir, possible_approach, model_name, task, "n_pass")
            if os.path.exists(task_dir):
                approach = possible_approach
                break
        else:
            task_dir = os.path.join(output_dir, approach, model_name, task, "n_pass")
    else:
        task_dir = os.path.join(output_dir, approach, model_name, task, "n_pass")
    
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
    # Set up argument parser
    parser = argparse.ArgumentParser(description='Analyze task results')
    parser.add_argument('--model_path', type=str, required=True,
                      help='Path to model folder (e.g., DeepSeek-R1 or output/SMT/DeepSeek-R1)')
    args = parser.parse_args()

    # Define tasks to analyze
    tasks = ["calendar", "trip", "meeting"]
    
    # Get approach from path
    approach = get_approach_from_path(args.model_path)
    model_name = os.path.basename(args.model_path)
    
    # Create output directory path
    output_dir = "../output"
    excel_dir = os.path.join(output_dir, approach, model_name)
    os.makedirs(excel_dir, exist_ok=True)
    
    # Create Excel writer with approach in filename
    output_file = os.path.join(excel_dir, f"task_analysis_results_{approach}_{model_name}.xlsx")
    
    # Track if we found any data
    found_data = False
    
    with pd.ExcelWriter(output_file, engine='openpyxl') as writer:
        for task in tasks:
            logging.info(f"Analyzing {task} results for {approach}/{model_name}")
            
            # Get analysis results
            summary_df, detailed_df = analyze_task_results(task, args.model_path)
            
            if summary_df is not None and not summary_df.empty:
                found_data = True
                # Write summary sheet
                sheet_name = f"{task}_{approach}_{model_name}_summary"
                summary_df.to_excel(writer, sheet_name=sheet_name, index=False)
                
                # Write detailed sheet
                sheet_name = f"{task}_{approach}_{model_name}_detailed"
                detailed_df.to_excel(writer, sheet_name=sheet_name, index=False)
                
                logging.info(f"Wrote {len(summary_df)} examples to {sheet_name}")
            else:
                logging.warning(f"No data found for {task} - {approach}/{model_name}")
    
    if not found_data:
        # If no data was found, delete the empty Excel file
        if os.path.exists(output_file):
            os.remove(output_file)
        logging.error("No data found for any task. No Excel file was created.")
    else:
        logging.info(f"Analysis complete. Results written to {output_file}")

if __name__ == "__main__":
    main() 