import os
import json
from pathlib import Path

def extract_code(response):
    """Extract Python code from a string, handling multiple formats."""
    if not response or response.isspace():
        return None, "empty_response"
    
    delimiters = ["```python", "```", "'''python", "'''"]
    
    # Try to find code block delimiters first
    for delimiter in delimiters:
        start = response.find(delimiter)
        if start != -1:
            start += len(delimiter)
            end = response.find(delimiter, start)
            if end != -1:
                code = response[start:end].strip()
                if code:  # Only return if we actually found code
                    # Remove any remaining "python" word at start
                    if code.startswith("python"):
                        code = code[6:].lstrip()
                    return code, "code_block"
    
    # Check for SOLUTION: prefix
    solution_prefix = "SOLUTION:"
    if solution_prefix in response:
        solution_code = response.split(solution_prefix, 1)[1].strip()
        if solution_code:  # Only return if there's actual content
            # Remove any remaining "python" word at start
            if solution_code.startswith("python"):
                solution_code = solution_code[6:].lstrip()
            return solution_code, "solution_prefix"
    
    # Check if this looks like raw Python code
    python_keywords = ["def ", "import ", "class ", "print(", "return ", "for ", "if "]
    if any(keyword in response for keyword in python_keywords):
        code = response.strip()
        # Remove any remaining "python" word at start
        if code.startswith("python"):
            code = code[6:].lstrip()
        return code, "raw_code"
    
    return None, "no_code"

def process_json_files(input_dir, output_dir):
    """Process JSON files and save extracted code with detailed reporting."""
    Path(output_dir).mkdir(parents=True, exist_ok=True)
    
    stats = {
        "processed": 0,
        "saved": 0,
        "no_code": 0,
        "extraction_failed": 0,
        "empty_responses": 0
    }
    
    for filename in os.listdir(input_dir):
        if not filename.endswith('.json'):
            continue
            
        filepath = os.path.join(input_dir, filename)
        stats["processed"] += 1
        
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                data = json.load(f)
            
            for item in data.get('0shot', []):
                raw_response = item.get('raw_model_response', '')
                count_value = item.get('count', 'unnamed')
                
                code, extraction_type = extract_code(raw_response)
                
                if extraction_type == "empty_response":
                    print(f"Note: Empty response in {filename}")
                    stats["empty_responses"] += 1
                elif extraction_type == "no_code":
                    print(f"Note: No code content in {filename} (count: {count_value})")
                    stats["no_code"] += 1
                elif code is None:
                    print(f"Warning: Extraction failed in {filename} (count: {count_value})")
                    stats["extraction_failed"] += 1
                else:
                    py_filename = f"{count_value}.py"
                    py_filepath = os.path.join(output_dir, py_filename)
                    
                    with open(py_filepath, 'w', encoding='utf-8') as f:
                        f.write(code)
                    
                    print(f"Saved: {py_filename} (source: {filename}, extraction: {extraction_type})")
                    stats["saved"] += 1
                    
        except Exception as e:
            print(f"Error processing {filename}: {str(e)}")
    
    print("\nProcessing complete! Statistics:")
    print(f"- Files processed: {stats['processed']}")
    print(f"- Python files saved: {stats['saved']}")
    print(f"- Empty responses: {stats['empty_responses']}")
    print(f"- No code content: {stats['no_code']}")
    print(f"- Extraction failures: {stats['extraction_failed']}")

if __name__ == "__main__":

    directory_model = 'DeepSeek-R1'
    task = 'trip'
    method = 'Python'
    input_directory = f"../output/{method}/{directory_model}/{task}/formatted_output"  # Change this to your input directory
    output_directory = f"../output/{method}/{directory_model}/{task}/code"  # Change this to your desired output directory
    
    process_json_files(input_directory, output_directory)
    print("Processing complete!")


