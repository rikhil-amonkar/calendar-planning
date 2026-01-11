"""
Enhanced Iterative SMT Refinement with Smart Code Extraction and Execution Handling

This script implements an iterative refinement process for solving scheduling problems using Z3 SMT solver.
It uses GPT for intelligent code extraction and execution result parsing, with comprehensive error handling.

Features:
1. Smart code extraction using GPT even when code blocks aren't properly formatted
2. Intelligent execution result parsing and formatting using GPT
3. Comprehensive error handling for different failure scenarios
4. Parallel processing with rate limiting
5. Detailed feedback generation for different error types

Directory structure for outputs:
../output/SMT/{model_name}/{task}/n_pass/{example_id}/{pass_number}_pass/
  - conversation.json: Full conversation history
  - solution.py: Generated Z3 code
  - output.out: Execution output
  - evaluation.json: Constraint evaluation results

Usage:
python iterative_smt_refinement_enhanced.py --task calendar --model DeepSeek-V3 --start 0 --end 5
python iterative_smt_refinement_enhanced.py --task trip --model gpt-4o-mini --examples '1009,1010'
python iterative_smt_refinement_enhanced.py --task zebralogic --model DeepSeek-V3 --examples '1,2,3'
"""

import argparse
import json
import os
import subprocess
import asyncio
import re
import time
from datetime import datetime
from kani import Kani
from kani.engines.huggingface import HuggingEngine
from kani.engines.openai import OpenAIEngine
import concurrent.futures
from typing import List, Dict, Any
import logging
import shutil
from openai import OpenAI
import tiktoken

import torch
torch.cuda.empty_cache()  # Clear cache
torch.backends.cudnn.benchmark = False  # Reduce memory usage

# Configure logging for timestamps
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

def parse_args():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(description="Run enhanced iterative SMT refinement with smart extraction")
    parser.add_argument("--model", type=str, required=True, help="Model to use (e.g., 'DeepSeek-R1')")
    parser.add_argument("--task", type=str, required=True, choices=["calendar", "trip", "meeting", "zebralogic"], help="Task type")
    parser.add_argument("--max_passes", type=int, default=1, help="Maximum number of refinement passes")
    parser.add_argument("--max_concurrent", type=int, default=10, help="Maximum number of concurrent examples to process")
    parser.add_argument("--rate_limit", type=int, default=60, help="Rate limit (requests per minute)")
    parser.add_argument("--start", type=int, help="Start example number (inclusive)")
    parser.add_argument("--end", type=int, help="End example number (exclusive)")
    parser.add_argument("--fresh", action="store_true", help="Clear all output directories before running")
    parser.add_argument("--examples", type=str, help="Comma-separated list of example numbers to run (e.g., '25,35')")
    
    args = parser.parse_args()
    
    # Clean up examples argument
    if args.examples:
        # Remove all quotes and whitespace
        args.examples = args.examples.replace('"', '').replace("'", "").strip()
        # Split and clean each number
        args.examples = ','.join(num.strip() for num in args.examples.split(','))
    
    return args

try:
    with open("../keys/deepseek_api_key.json") as f:
        keys = json.load(f)
except FileNotFoundError:
    print("Error: openai_research/deepseek_api_key.json not found. Please create this file with your API keys.")
    exit(1)

def initialize_model(model_name, keys):
    """Initializes the Kani AI model based on the model name."""
    if model_name.startswith("gpt") or model_name.startswith("o"):
        if model_name == "o3-mini":
            model_name = "o3-mini"
        elif model_name == "gpt-4o-mini":
            model_name = "gpt-4o-mini-2024-07-18"
        elif model_name == "gpt-5-2025-08-07":
            model_name = "gpt-5-2025-08-07"
        engine = OpenAIEngine(keys["openai"], model=model_name, max_context_size=20000)
    elif model_name == "DeepSeek-R1":
        engine = OpenAIEngine(keys["deepseek"], model="deepseek-reasoner", api_base="https://api.deepseek.com", max_context_size=20000)
    elif model_name == "DeepSeek-V3":
        engine = OpenAIEngine(keys["deepseek"], model="deepseek-chat", api_base="https://api.deepseek.com", max_context_size=20000)
    else:
        engine = HuggingEngine(model_id=model_name)

    ai = Kani(engine, system_prompt="")
    return ai

def get_openai_client():
    """Get OpenAI client for GPT-based extraction"""
    try:
        with open("../keys/deepseek_api_key.json") as f:
            key = json.load(f)["openai"]
        return OpenAI(api_key=key)
    except (FileNotFoundError, KeyError):
        logging.warning("Could not initialize OpenAI client for extraction")
        return None

def smart_extract_code(response_txt):
    """
    Smart code extraction using GPT when traditional regex fails
    """
    # First try traditional regex extraction
    matches = re.findall(r"```python\s*(.*?)```", response_txt, re.DOTALL)
    if matches:
        return matches[-1].strip()
    
    # If no code blocks found, try to extract code using GPT
    client = get_openai_client()
    if not client:
        logging.warning("OpenAI client not available, falling back to basic extraction")
        return ""
    
    try:
        prompt = f"""Extract the Python code from the following text. Look for any Python code that might solve a scheduling problem using Z3 solver.

Text:
{response_txt}

If you find Python code, return ONLY the code without any markdown formatting or explanations.
If no Python code is found, return an empty string.

Focus on:
1. Code that imports and uses Z3 solver
2. Code that defines variables, constraints, and solves problems
3. Code that prints or returns results

Return only the Python code:"""

        response = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role": "user", "content": prompt}],
            temperature=0,
            max_tokens=2000
        )
        
        extracted_code = response.choices[0].message.content.strip()
        
        # Clean up the extracted code
        if extracted_code.startswith("```python"):
            extracted_code = extracted_code[9:]
        if extracted_code.endswith("```"):
            extracted_code = extracted_code[:-3]
        
        return extracted_code.strip()
        
    except Exception as e:
        logging.error(f"Error in smart code extraction: {e}")
        return ""

def smart_extract_execution_result(execution_output, task):
    """
    Smart extraction of execution results using GPT
    Handles various output formats including errors and no-plan scenarios
    """
    client = get_openai_client()
    if not client:
        logging.warning("OpenAI client not available, falling back to basic extraction")
        return extract_answer_basic(execution_output, task)
    
    try:
        # Determine the expected output format based on task
        if task == "calendar":
            expected_format = '{"day": "Monday", "start_time": "14:30", "end_time": "15:30"}'
        elif task == "trip":
            expected_format = '{"itinerary": [{"day_range": "Day 1-3", "place": "Venice"}, {"day_range": "Day 3-5", "place": "Vienna"}]}'
        elif task == "meeting":
            expected_format = '{"itinerary": [{"action": "meet", "person": "David", "start_time": "13:00", "end_time": "14:00"}]}'
        elif task == "zebralogic":
            expected_format = '{"solution": {"header": ["House", "Color", "Nationality", "Drink", "Smoke", "Pet"], "rows": [["1", "Yellow", "Norwegian", "Water", "Kools", "Fox"], ["2", "Blue", "Ukrainian", "Tea", "Chesterfield", "Horse"]]}}'
        
        prompt = f"""Extract structured data from the following execution output for a {task} planning task.

Execution Output:
{execution_output}

Expected format: {expected_format}

Instructions:
1. If the output contains valid JSON in the expected format, extract and return it
2. If the output indicates no plan was found or if the output is empty (like "", "No valid itinerary found", "No solution found", "UNSAT", "unsat", etc.), return {{"no_plan": "reason"}}
3. If the output contains an execution error message (like "Error:", "Exception:", "Traceback:", etc.), return {{"error": "error_message"}}
4. If the output is malformed or unclear, try to extract any useful information or return {{"error": "malformed_output"}}

Return only valid JSON:"""

        response = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role": "user", "content": prompt}],
            response_format={"type": "json_object"},
            temperature=0,
            max_tokens=2000
        )
        
        result = json.loads(response.choices[0].message.content)
        return result
        
    except Exception as e:
        logging.error(f"Error in smart execution result extraction: {e}")
        return extract_answer_basic(execution_output, task)

def extract_answer_basic(answer_str, task):
    """Basic extraction fallback - same as original script"""
    from openai import OpenAI
    
    try:
        with open("../keys/deepseek_api_key.json") as f:
            key = json.load(f)["openai"]
        client = OpenAI(api_key=key)
    except (FileNotFoundError, KeyError):
        print("Warning: Could not initialize OpenAI client for answer extraction")
        return {}
    
    # If answer_str is None or empty, return empty dict
    if not answer_str:
        return {}
    
    # For calendar task, try to extract from natural language format first
    if task == "calendar":
        patterns = [
            r"(?:Here is the proposed time:|SOLUTION:?|Time:?|Meeting:?)\s*(?:Day:?\s*)?([A-Za-z]+)(?:,?\s*|,\s*)(\d{1,2}:\d{2})\s*(?:-|to)\s*(\d{1,2}:\d{2})",
            r"([A-Za-z]+)(?:,?\s*|,\s*)(\d{1,2}:\d{2})\s*(?:-|to)\s*(\d{1,2}:\d{2})",
            r"Day:\s*([A-Za-z]+)\s*\nStart Time:\s*(\d{1,2}:\d{2})\s*\nEnd Time:\s*(\d{1,2}:\d{2})",
            r"Day:\s*([A-Za-z]+)\s*Start Time:\s*(\d{1,2}:\d{2})\s*End Time:\s*(\d{1,2}:\d{2})"
        ]
        
        for pattern in patterns:
            match = re.search(pattern, answer_str, re.IGNORECASE | re.MULTILINE)
            if match:
                day = match.group(1).strip()
                start_time = match.group(2).strip()
                end_time = match.group(3).strip()
                
                # Convert to 24-hour format if needed
                if "PM" in answer_str and int(start_time.split(':')[0]) < 12:
                    start_hour = int(start_time.split(':')[0]) + 12
                    start_time = f"{start_hour:02d}:{start_time.split(':')[1]}"
                if "PM" in answer_str and int(end_time.split(':')[0]) < 12:
                    end_hour = int(end_time.split(':')[0]) + 12
                    end_time = f"{end_hour:02d}:{end_time.split(':')[1]}"
                if "AM" in answer_str and int(start_time.split(':')[0]) == 12:
                    start_time = f"00:{start_time.split(':')[1]}"
                if "AM" in answer_str and int(end_time.split(':')[0]) == 12:
                    end_time = f"00:{end_time.split(':')[1]}"
                
                return {
                    "day": day,
                    "start_time": start_time,
                    "end_time": end_time
                }
    
    # For meeting task, try to extract meeting information
    if task == "meeting":
        meetings = []
        lines = answer_str.split('\n')
        for line in lines:
            patterns = [
                r"Meet\s+(\w+)\s+(?:at\s+)?(?:[^(]+)?(?:\([^)]+\))?\s+from\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?\s+to\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?",
                r"Meet\s+(\w+)\s+(?:at\s+)?(?:[^(]+)?(?:\([^)]+\))?\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?\s+to\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?",
                r"(\w+):\s+from\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?\s+to\s+(\d{1,2}:\d{2})\s+(?:AM|PM)?",
                r"You meet (\w+) for \d+ minutes from (\d{1,2}:\d{2})(?:AM|PM)? to (\d{1,2}:\d{2})(?:AM|PM)?",
                r"meet (\w+) for \d+ minutes from (\d{1,2}:\d{2})(?:AM|PM)? to (\d{1,2}:\d{2})(?:AM|PM)?"
            ]
            
            for pattern in patterns:
                match = re.search(pattern, line, re.IGNORECASE)
                if match:
                    person = match.group(1)
                    start_time = match.group(2)
                    end_time = match.group(3)
                    
                    # Convert to 24-hour format if needed
                    if "PM" in line and int(start_time.split(':')[0]) < 12:
                        start_hour = int(start_time.split(':')[0]) + 12
                        start_time = f"{start_hour:02d}:{start_time.split(':')[1]}"
                    if "PM" in line and int(end_time.split(':')[0]) < 12:
                        end_hour = int(end_time.split(':')[0]) + 12
                        end_time = f"{end_hour:02d}:{end_time.split(':')[1]}"
                    if "AM" in line and int(start_time.split(':')[0]) == 12:
                        start_time = f"00:{start_time.split(':')[1]}"
                    if "AM" in line and int(end_time.split(':')[0]) == 12:
                        end_time = f"00:{end_time.split(':')[1]}"
                    
                    meetings.append({
                        "action": "meet",
                        "person": person,
                        "start_time": start_time,
                        "end_time": end_time
                    })
                    break
        
        if meetings:
            return {"itinerary": meetings}
    
    # For ZebraLogic task, try to extract structured solution
    if task == "zebralogic":
        # First try to find JSON in the output
        json_pattern = r'\{.*?"solution"\s*:\s*\{.*?"header"\s*:\s*\[.*?\],\s*"rows"\s*:\s*\[.*?\]\}.*?\}'
        matches = re.search(json_pattern, answer_str, re.DOTALL)
        if matches:
            try:
                return json.loads(matches.group(0))
            except json.JSONDecodeError:
                pass
        
        # If no JSON found, try to parse as table
        table_pattern = r'House\s*\|\s*(\w+)\s*\|\s*(\w+)\s*\|\s*(\w+)\s*\|\s*(\w+)\s*\|\s*(\w+)'
        headers = ["House"]
        if re.search(table_pattern, answer_str):
            # Extract headers
            header_match = re.search(table_pattern, answer_str)
            headers.extend(header_match.groups())
            
            # Extract rows
            rows = []
            row_pattern = r'(\d+)\s*\|\s*([^\|]+)\s*\|\s*([^\|]+)\s*\|\s*([^\|]+)\s*\|\s*([^\|]+)\s*\|\s*([^\|]+)'
            for row_match in re.finditer(row_pattern, answer_str):
                rows.append(list(row_match.groups()))
            
            if rows:
                return {
                    "solution": {
                        "header": headers,
                        "rows": rows
                    }
                }
    
    # For trip task, use the revised format and instructions
    prompt = {
        "calendar": "Given the following time range:\n" + answer_str + "\nExtract the meeting start day and time in a JSON like {\"day\": \"Monday\", \"start_time\": \"14:30\", \"end_time\": \"15:30\"}. The time should be in 24-hour format. If no time range is given at all, output an empty JSON.",
        "trip": (
            "Given the following itinerary:\n" + answer_str +
            "\nExtract the days spent in each city in a JSON format like "
            "{\"itinerary\": [{\"day_range\": \"Day 1-4\", \"place\": \"Tallinn\"}, {\"day_range\": \"Day 4-6\", \"place\": \"Munich\"}]}. "
            "Each entry should represent a continuous stay in a city, with the day range inclusive. "
            "IMPORTANT: When you fly from city A to city B on day X, that day counts for BOTH cities. "
            "For example:\n"
            "- If you stay in Venice from Day 1-3 and fly to Vienna on Day 3, then:\n"
            "  - Venice: Day 1-3 (3 days)\n"
            "  - Vienna: Day 3-6 (4 days, including the flight day)\n"
            "- The flight day (Day 3) is counted for both Venice and Vienna.\n"
            "- Do NOT create separate flight entries in the JSON.\n"
            "If no itinerary is given, output an empty JSON."
        ),
        "meeting": "Given the following meeting schedule:\n" + answer_str + "\nExtract the time and the person of each meeting in a JSON format like {\"itinerary\": [{\"action\": \"meet\", \"person\": \"David\",\"start_time\": \"13:00\", \"end_time\": \"14:00\"}, ...]}. Do not include location. Only keep the meeting times, and ignore time for starting, waiting, or traveling. The time should be converted to a 24-hour format. If no time range is given at all, output an empty JSON",
        "zebralogic": (
            "Given the following puzzle solution:\n" + answer_str + 
            "\nExtract the solution in a JSON format that exactly matches the expected output structure. "
            "The JSON must contain a 'solution' key with 'header' and 'rows' arrays. "
            "Example of required format:\n"
            "{\n"
            '  "solution": {\n'
            '    "header": ["House", "Color", "Nationality", "Drink", "Smoke", "Pet"],\n'
            '    "rows": [\n'
            '      ["1", "Yellow", "Norwegian", "Water", "Kools", "Fox"],\n'
            '      ["2", "Blue", "Ukrainian", "Tea", "Chesterfield", "Horse"]\n'
            '    ]\n'
            "  }\n"
            "}\n\n"
            "Important:\n"
            "- Keep all original values exactly as provided\n"
            "- Maintain correct house ordering (1, 2, 3...)\n"
            "- Include all attributes in each row\n"
            "- If no valid solution is given, output empty JSON {}\n"
            "- Do not include any explanatory text, only the JSON"
        )
    }
    
    try:
        response = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role": "user", "content": prompt[task]}],
            response_format={"type": "json_object"},
            temperature=0,
            max_tokens=2000
        )
        output_json = response.choices[0].message.content
        return json.loads(output_json)
    except Exception as e:
        print(f"Error in answer extraction: {e}")
        return {}

def normalize_trip_itinerary(itinerary):
    """Normalize trip itinerary for comparison by sorting segments and removing duplicates"""
    if not itinerary or "itinerary" not in itinerary:
        return itinerary
    
    segments = itinerary["itinerary"]
    
    # Sort segments by start day, then by place
    sorted_segments = sorted(segments, key=lambda x: (
        int(x["day_range"].replace("Day ", "").split("-")[0]), 
        x["place"]
    ))
    
    return {"itinerary": sorted_segments}

def parse_zebralogic_golden(golden_plan):
    """Parse the golden solution into a structured format."""
    if not isinstance(golden_plan, dict) or "rows" not in golden_plan:
        return {"error": "Invalid golden plan format"}
    
    # Convert the table format to a list of dicts
    solution = []
    headers = golden_plan["header"]
    for row in golden_plan["rows"]:
        solution.append(dict(zip(headers, row)))
    return solution

def parse_zebralogic_output(output):
    """Parse model output into structured format: list[dict] per house."""
    if not output:
        return None

    try:
        # Try to parse as JSON first
        if isinstance(output, str):
            try:
                output = json.loads(output)
            except json.JSONDecodeError:
                # Look for JSON within the output string
                json_match = re.search(r'\{.*\}', output, re.DOTALL)
                if json_match:
                    output = json.loads(json_match.group(0))
        
        if isinstance(output, dict):
            # Get solution from either top level or 'solution' key
            solution = output.get("solution", output)
            
            if "header" in solution and "rows" in solution:
                headers = solution["header"]
                rows = solution["rows"]
                
                # Convert to list of dicts
                result = []
                for row in rows:
                    if len(row) != len(headers):
                        continue
                    result.append(dict(zip(headers, row)))
                return result
    except Exception as e:
        logging.warning(f"Error parsing ZebraLogic output: {e}")
    
    return None

def evaluate_zebralogic(constraints, predicted_output):
    """Evaluate ZebraLogic solution with more robust comparison"""
    if not predicted_output or not isinstance(predicted_output, list):
        return False, {"invalid_output": "No valid output structure found"}
    
    golden_output = parse_zebralogic_golden(constraints.get("golden_plan", {}))
    
    if not isinstance(golden_output, list):
        return False, {"invalid_golden": "Invalid golden solution format"}
    
    # First check for exact match (string comparison of sorted JSON)
    try:
        pred_str = json.dumps(predicted_output, sort_keys=True)
        gold_str = json.dumps(golden_output, sort_keys=True)
        if pred_str == gold_str:
            return True, {}
    except Exception:
        pass
    
    # If not exact match, do field-by-field comparison
    violations = []
    
    # Check structure matches
    if len(predicted_output) != len(golden_output):
        violations.append(f"Wrong number of houses: expected {len(golden_output)}, got {len(predicted_output)}")
    
    # Check each house
    for house_num, (gold_house, pred_house) in enumerate(zip(golden_output, predicted_output), 1):
        if not isinstance(pred_house, dict):
            violations.append(f"House {house_num} is not a valid dictionary")
            continue
            
        # Check all fields in golden exist in predicted (case insensitive)
        for field, gold_value in gold_house.items():
            field_lower = field.lower()
            pred_fields = {k.lower(): v for k, v in pred_house.items()}
            
            if field_lower not in pred_fields:
                violations.append(f"House {house_num} missing field '{field}'")
            else:
                pred_value = pred_house.get(field)  # Use original case for comparison
                if str(pred_value).strip().lower() != str(gold_value).strip().lower():
                    violations.append(
                        f"House {house_num} wrong {field}: expected '{gold_value}', got '{pred_value}'"
                    )
    
    if violations:
        return False, {"violations": violations}
    return True, {}

def format_zebralogic_feedback(violated_constraints):
    if not violated_constraints:
        return ""
    
    feedback = ["\nYour solution has the following issues:"]
    
    if "violations" in violated_constraints:
        feedback.extend(f"- {v}" for v in violated_constraints["violations"][:10])  # Limit to 10 violations
    else:
        for k, v in violated_constraints.items():
            if k != "differences":  # Skip GPT-generated differences which may be unreliable
                feedback.append(f"- {k}: {v}")
    
    feedback.append("\nPlease revise to match all attributes exactly.")
    return "\n".join(feedback)

# Build evaluation functions directly in this file
def execute_python_code(code_path):
    """Execute Python code and return the output"""
    try:
        result = subprocess.run(['python3', code_path], capture_output=True, text=True, timeout=30)
        return result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return "Execution timeout"
    except Exception as e:
        return f"Execution error: {str(e)}"

def format_constraint_feedback(violated_constraints):
    """Format constraint violations into feedback"""
    if not violated_constraints:
        return ""
    
    feedback = "The following constraints are violated:\n"
    for constraint, details in violated_constraints.items():
        feedback += f"- {constraint}: {details}\n"
    return feedback

def evaluate_calendar(constraints, pred_dict):
    # Check for no_plan cases first
    if isinstance(pred_dict, dict) and ("no_plan" in pred_dict or "error" in pred_dict):
        return False, {"no_plan": pred_dict.get("no_plan", pred_dict.get("error", "unknown"))}
    
    # Check for missing day, start_time, or end_time
    if not pred_dict or "day" not in pred_dict or "start_time" not in pred_dict or "end_time" not in pred_dict:
        return False, {"missing_fields": True}
    
    pred_day = pred_dict["day"]
    pred_start = pred_dict["start_time"]
    pred_end = pred_dict["end_time"]
    
    # Check for None values in any of the fields
    if pred_day is None or pred_start is None or pred_end is None:
        return False, {"null_fields": True}
    
    # Convert time strings to numerical values
    if isinstance(pred_start, str):
        pred_start_parts = pred_start.split(":")
        try:
            pred_start = float(pred_start_parts[0]) + float(pred_start_parts[1]) / 60
        except ValueError:
            return False, {"unparsable": True}
    if isinstance(pred_end, str):
        pred_end_parts = pred_end.split(":")
        try:
            pred_end = float(pred_end_parts[0]) + float(pred_end_parts[1]) / 60
        except ValueError:
            return False, {"unparsable": True}
    meeting_duration = constraints.get("meeting_duration")
    if meeting_duration is None:
        return False, {"missing_meeting_duration": True}
    if (pred_end - pred_start) != meeting_duration:
        return False, {"meeting_duration": meeting_duration}
    for disallowed_range in constraints.get("disallowed_ranges", []):
        if disallowed_range["day"] == pred_day:
            if (pred_start >= disallowed_range["start"] and pred_start < disallowed_range["end"]) or \
               (pred_end > disallowed_range["start"] and pred_end <= disallowed_range["end"]) or \
               (pred_start <= disallowed_range["start"] and pred_end >= disallowed_range["end"]):
                return False, disallowed_range
    return True, {}

def evaluate_trip(constraints, pred_dict):
    # Check for no_plan cases first
    if isinstance(pred_dict, dict) and ("no_plan" in pred_dict or "error" in pred_dict):
        return False, {"no_plan": pred_dict.get("no_plan", pred_dict.get("error", "unknown"))}
    
    # parse the predicted itinerary segments
    segments = []
    for seg in pred_dict["itinerary"]:
        # Handle special cases like "Day {current_day}-{current_day + 2}"
        if not seg["day_range"].startswith("Day ") or "{" in seg["day_range"] or "}" in seg["day_range"]:
            return False, {"invalid_day_range_format": seg["day_range"]}
        # "Day X-Y"
        dr = seg["day_range"].replace("Day ", "")
        if "-" in dr:
            start_s, end_s = dr.split("-")
        else:
            start_s, end_s = [dr, dr]
        try:
            start, end = int(start_s), int(end_s)
        except ValueError:
            return False, {"unparsable_day_range": seg["day_range"]}
        segments.append({"place": seg["place"], "start": start, "end": end})
    
    # Sort segments by start day to ensure chronological order for constraint evaluation
    segments.sort(key=lambda x: x["start"])
    
    # 1) check full coverage from day 1 to total_days, with no gaps/overlaps
    total = constraints.get("trip_length")
    if not segments or segments[0]["start"] != 1 or segments[-1]["end"] != total:
        return False, {"total_days": total}
    for a, b in zip(segments, segments[1:]):
        if a["end"] != b["start"]:
            return False, {"gap/overlap": (a, b)}
    
    # 2) check each place's stay duration
    # Handle both 'stay_days' (dict) and 'city_length' (array) formats
    stay_days_dict = {}
    if "stay_days" in constraints:
        stay_days_dict = constraints["stay_days"]
    elif "city_length" in constraints:
        for city_info in constraints["city_length"]:
            stay_days_dict[city_info["city"]] = city_info["days"]
    
    for seg in segments:
        required = stay_days_dict.get(seg["place"])
        if required is not None:
            actual = seg["end"] - seg["start"] + 1
            if actual != required:
                return False, {"stay_days": {seg["place"]: required}}
    
    # 3) check event_ranges (must fall entirely within the visit segment)
    for ev in constraints.get("city_day_ranges", []):
        place = ev["city"]
        container = next((s for s in segments if s["place"] == place), None)
        if not container:
            return False, {"missing_place": place}
        if container["start"] > ev["start"] or container["end"] < ev["end"]:
            return False, {"event_range": ev}
    
    # 4) check flight connectivity between consecutive places
    allowed = [(d["from"], d["to"]) for d in constraints.get("direct_flights", [])]
    for a, b in zip(segments, segments[1:]):
        pair = (a["place"], b["place"])
        if pair not in allowed:
            return False, {"flight": {"from": a["place"], "to": b["place"]}}
    
    return True, {}

def evaluate_meeting(constraints, pred_dict):
    from datetime import datetime

    def parse_time(s):
        # Return None for invalid time formats instead of raising exception
        try:
            # handles "H:MM" or "H:MMAM"/"H:MMPM"
            if s.endswith(("AM", "PM")):
                return datetime.strptime(s, "%I:%M%p")
            return datetime.strptime(s, "%H:%M")
        except ValueError:
            return None

    # Check for no_plan cases first
    if isinstance(pred_dict, dict) and ("no_plan" in pred_dict or "error" in pred_dict):
        return False, {"no_plan": pred_dict.get("no_plan", pred_dict.get("error", "unknown"))}

    # build map person→availability & location
    people = {p["name"]: p for p in constraints.get("people_to_meet", [])}
    start_location = constraints.get("start", {}).get("location")
    start_time = constraints.get("start", {}).get("time_of_day")
    num_people_to_meet = constraints.get("num_people_to_meet", 0)

    # parse predicted meetings
    meetings = []
    for m in pred_dict.get("itinerary", []):
        name = m["person"]
        start = parse_time(m["start_time"])
        end = parse_time(m["end_time"])
        if start is None or end is None:  # Invalid time format
            return False, {"invalid_time_format": {"start": m["start_time"], "end": m["end_time"]}}
        loc = people.get(name, {}).get("location")
        meetings.append({"person": name, "start": start, "end": end, "location": loc})

    if len(meetings) < num_people_to_meet:
        return False, {"num_people_to_meet": num_people_to_meet}
    # sort chronologically
    meetings.sort(key=lambda x: x["start"])

    # 1) each meeting must lie within that person's available window
    for m in meetings:
        p = people.get(m["person"])
        if not p:
            continue
        avail = p["time_of_day"]
        av_from = parse_time(avail["from"])
        av_to = parse_time(avail["to"])
        if m["start"] < av_from or m["end"] > av_to:
            return False, {"person": m["person"], "time_of_day": avail}

    # 2) build travel‐time lookup
    travel = {}
    for d in constraints.get("travel_distances", []):
        pl = d["place"]
        frm = pl.get("from", constraints.get("start", {}).get("location"))
        to = pl["to"]
        travel[(frm, to)] = d["walking_time"]

    # 3) check start‐to‐first meeting
    # parse start time
    if start_time and meetings:
        st = parse_time(start_time)
        first = meetings[0]
        # 0a) meeting must not start before you arrive
        if first["start"] < st:
            return False, {"start_time": start_time}
        # 0b) travel from start_location
        walk0 = travel.get((start_location, first["location"]))
        gap0 = (first["start"] - st).total_seconds() / 60
        if walk0 is not None and walk0 > gap0:
            return False, {
                "travel_start": {
                    "to_person": first["person"],
                    "to_location": first["location"],
                    "travel_time": walk0
                }
            }

    # 3) check following meetings
    for a, b in zip(meetings, meetings[1:]):
        gap_mins = (b["start"] - a["end"]).total_seconds() / 60
        walk = travel.get((a["location"], b["location"]))
        if walk is not None and walk > gap_mins:
            return False, {
                "travel": {
                    "from_person": a["person"],
                    "to_person": b["person"],
                    "from_location": a["location"],
                    "to_location": b["location"],
                    "travel_time": walk
                }
            }

    return True, {}

eval_functions = {
    "calendar": evaluate_calendar,
    "trip": evaluate_trip,
    "meeting": evaluate_meeting,
    "zebralogic": evaluate_zebralogic
}

feedback_functions = {
    "calendar": format_constraint_feedback,
    "trip": format_constraint_feedback,
    "meeting": format_constraint_feedback,
    "zebralogic": format_zebralogic_feedback
}

task_name_map = {
    "calendar": "calendar_scheduling",
    "trip": "trip_planning",
    "meeting": "meeting_planning",
    "zebralogic": "zebralogic"
}

class RateLimiter:
    """Simple rate limiter to avoid API limits"""
    def __init__(self, requests_per_second: float):
        self.requests_per_second = requests_per_second
        self.last_request_time = 0
    
    async def wait(self):
        if self.requests_per_second <= 0:
            return
        
        current_time = time.time()
        time_since_last = current_time - self.last_request_time
        min_interval = 1.0 / self.requests_per_second
        
        if time_since_last < min_interval:
            wait_time = min_interval - time_since_last
            await asyncio.sleep(wait_time)
        
        self.last_request_time = time.time()

async def run_model_with_rate_limit(ai, prompt, rate_limiter):
    """Run the AI model with rate limiting"""
    await rate_limiter.wait()
    response = await ai.chat_round_str(prompt)
    return response 

def count_tokens(text):
    """Count tokens in text with fallback to character count if tiktoken fails"""
    try:
        # Define the model (e.g., "gpt-3.5-turbo" or "gpt-4")
        model_name = "gpt-4o"  # this doesn't matter for DeepSeek models
        # Initialize the encoder for the specific model
        encoding = tiktoken.encoding_for_model(model_name)
        # Document to be tokenized
        document = f"{text}"
        # Count the tokens
        tokens = encoding.encode(document)
        token_count = len(tokens)
        return token_count
    except Exception as e:
        logging.warning(f"Token counting failed, using fallback method: {str(e)}")
        return len(text)

def extract_reasoning(response, model_name):
    """Extract reasoning content from model response for HuggingFace models (like Qwen2.5)"""
    reasoning_content = ""
    reasoning_tokens = 0
    
    # For HuggingFace models (like Qwen2.5), extract reasoning from response text
    # Qwen2.5 reasoning models may output reasoning in <reasoning> tags or before code blocks
    if response:
        # First, try to extract from <reasoning> tags (Qwen2.5 reasoning format)
        reasoning_match = re.search(r'<reasoning>(.*?)</reasoning>', response, re.DOTALL | re.IGNORECASE)
        if reasoning_match:
            reasoning_content = reasoning_match.group(1).strip()
            logging.info(f"Extracted reasoning from <reasoning> tags: {len(reasoning_content)} chars")
        else:
            # Fallback: Try <think> tags (matching test_qwen25_reasoning.py)
            think_match = re.search(r'<think>(.*?)</think>', response, re.DOTALL | re.IGNORECASE)
            if think_match:
                reasoning_content = think_match.group(1).strip()
                logging.info(f"Extracted reasoning from <think> tags: {len(reasoning_content)} chars")
            else:
                # Fallback: Extract reasoning from text before code blocks
                code_start = response.find("```")
                if code_start > 50:  # If there's substantial text before code
                    potential_reasoning = response[:code_start].strip()
                    # Check if it looks like reasoning (contains analysis keywords or is substantial)
                    reasoning_keywords = ["think", "analyze", "consider", "reason", "approach", "strategy", 
                                         "understand", "need", "must", "should", "constraint", "solution",
                                         "first", "then", "because", "therefore", "step", "problem",
                                         "given", "calculate", "determine", "find", "solve"]
                    # If it's substantial text (more than 50 chars) and contains reasoning keywords
                    if len(potential_reasoning) > 50 and any(keyword in potential_reasoning.lower() for keyword in reasoning_keywords):
                        reasoning_content = potential_reasoning
                        logging.info(f"Extracted reasoning from response text before code: {len(reasoning_content)} chars")
                    elif len(potential_reasoning) > 200:  # Very substantial text is likely reasoning
                        reasoning_content = potential_reasoning
                        logging.info(f"Extracted reasoning from substantial pre-code text: {len(reasoning_content)} chars")
    
    # Count reasoning tokens
    if reasoning_content:
        reasoning_tokens = count_tokens(reasoning_content)
        logging.info(f"Extracted {reasoning_tokens} reasoning tokens from {model_name} response")
    else:
        reasoning_tokens = 0
        logging.warning(f"No reasoning content found in {model_name} response (response length: {len(response) if response else 0} chars)")
    
    return reasoning_content, reasoning_tokens

def check_example_complete(task, example_id, model_name):
    """Check if an example has been fully completed by verifying output files exist and are valid."""
    output_base = f"../output/SMT/{model_name}/{task}/token_pass/{example_id}"
    # Resolve to absolute path to avoid issues with relative paths
    output_base = os.path.abspath(output_base)
    if not os.path.exists(output_base):
        logging.debug(f"Output folder does not exist: {output_base}")
        return False
    
    logging.debug(f"Checking completeness for {output_base}")
    
    # Check all pass directories
    try:
        pass_dirs = [d for d in os.listdir(output_base) if d.endswith("_pass") and os.path.isdir(os.path.join(output_base, d))]
    except Exception as e:
        logging.warning(f"Error listing pass directories in {output_base}: {e}")
        return False
    
    if not pass_dirs:
        return False
    
    # Check each pass has required files and is complete
    required_files = ["evaluation.json", "conversation.json", "solution.py"]
    for pass_dir in sorted(pass_dirs):  # Process in order
        pass_path = os.path.join(output_base, pass_dir)
        eval_file = os.path.join(pass_path, "evaluation.json")
        
        # Check if evaluation.json exists and is valid
        if not os.path.exists(eval_file):
            logging.debug(f"Missing evaluation.json in {pass_path} - example incomplete")
            return False
        
        try:
            with open(eval_file, 'r') as f:
                eval_data = json.load(f)
            # Check required fields exist
            if "status" not in eval_data or "pass_number" not in eval_data:
                logging.debug(f"Invalid evaluation.json structure in {pass_path} - missing required fields")
                return False
            # Check if it's a valid completion (not an error state that needs retry)
            # Note: We allow all statuses as long as the pass completed (file saved)
        except (json.JSONDecodeError, Exception) as e:
            logging.debug(f"Invalid or corrupted evaluation.json in {pass_path}: {e}")
            return False
        
        # Check other required files exist
        for req_file in required_files:
            req_path = os.path.join(pass_path, req_file)
            if not os.path.exists(req_path):
                logging.debug(f"Missing required file {req_file} in {pass_path} - example incomplete")
                return False
            # For solution.py, check it's not empty (was actually generated)
            if req_file == "solution.py":
                try:
                    if os.path.getsize(req_path) == 0:
                        logging.debug(f"Empty solution.py in {pass_path} - example incomplete")
                        return False
                except Exception:
                    pass
    
    # All passes have required files - example is complete
    logging.debug(f"Example {example_id} has complete output files in {output_base} ({len(pass_dirs)} pass(es))")
    return True

def clear_incomplete_example(task, example_id, model_name):
    """Clear output folder for an incomplete example."""
    output_base = f"../output/SMT/{model_name}/{task}/token_pass/{example_id}"
    output_base = os.path.abspath(output_base)  # Use absolute path for consistency
    if os.path.exists(output_base):
        try:
            shutil.rmtree(output_base)
            logging.info(f"Cleared incomplete output folder: {output_base}")
            return True
        except Exception as e:
            logging.error(f"Failed to clear incomplete folder {output_base}: {e}")
            return False
    return False

async def process_single_example(
    example_id,
    example,
    constraints,
    model,
    max_passes,
    rate_limiter,
    semaphore,
    task,
    args
):
    """Process a single example with enhanced error handling and smart feedback"""
    # Initialize variables that might be referenced in error handling
    gold_formatted = {}
    pred_formatted = {}
    violated_constraints = {}
    is_exact_match = False
    constraints_satisfied = False
    execution_output = ""
    pass_num = 0
    
    async with semaphore:
        try:
            # Get task prefix for output directory
            task_prefix = task_name_map[task]
            
            # Verify example_id matches task prefix
            if not example_id.startswith(f"{task_prefix}_example_"):
                logging.warning(f"Example ID {example_id} does not match expected format for task {task}, skipping")
                return
            
            output_dir = f"../output/SMT/{model}/{task}/token_pass/{example_id}"
            
            # CRITICAL: Double-check if this example is already complete before making any API calls
            # This prevents duplicate requests if tasks were queued before output files were created
            if not args.fresh:
                output_path = os.path.abspath(output_dir)
                if check_example_complete(task, example_id, model):
                    logging.info(f"[SKIP] {task}/{example_id} already has complete output files at {output_path} - skipping to avoid duplicate API calls")
                    return
                # Additional safety check: verify output folder doesn't exist or is empty
                if os.path.exists(output_path):
                    # Folder exists but check_example_complete returned False - something is incomplete
                    logging.warning(f"[REDO] {task}/{example_id} has incomplete output at {output_path} - should have been cleared in main(), clearing now...")
                    clear_incomplete_example(task, example_id, model)
            
            os.makedirs(output_dir, exist_ok=True)
            
            logging.info(f"[{example_id}] Starting processing with model {model}")
            logging.info(f"[{example_id}] Output directory: {output_dir}")
            
            # Initialize AI model
            try:
                with open("../keys/deepseek_api_key.json") as f:
                    keys = json.load(f)
                ai = initialize_model(model, keys)
                logging.info(f"[{example_id}] Model initialized successfully")
            except Exception as e:
                logging.error(f"[{example_id}] Failed to initialize model: {str(e)}")
                # Save error evaluation result
                error_eval_result = {
                    "has_execution_error": True,
                    "execution_output": f"Model initialization failed: {str(e)}",
                    "pred": {},
                    "gold": {},
                    "status": "Model initialization error",
                    "violated_constraint": {},
                    "is_exact_match": False,
                    "constraints_satisfied": False,
                    "pass_number": 0
                }
                with open(f"{output_dir}/1_pass/evaluation.json", "w") as f:
                    json.dump(error_eval_result, f, indent=4)
                return
            
            # Initialize conversation history
            conversation_history = []
            
            # Initial prompt
            prompt_prep_start = time.time()
            initial_prompt = "Given the following scheduling problem:\n"
            initial_prompt += f"{example['prompt_0shot']}\n"

            if task == "calendar":
                initial_prompt += "Your solution should always have three things: the day to meet, the start time, and the end time.\n"
                initial_prompt += "Your output should be a string that starts with 'SOLUTION:' followed by three lines in this exact format:\nDay: <day>\nStart Time: <HH:MM> (24-hour format)\nEnd Time: <HH:MM> (24-hour format)\n"
            elif task == "trip":
                initial_prompt += "Note that if one flies from city A to city B on day X, then they are in both cities A and B on day X, which contributes to the total number of days in each city.\n"
                initial_prompt += "Your output should be a JSON-formatted dictionary with an 'itinerary' key containing a list of day-place mappings.\n"
                initial_prompt += "Do not include separate flight entries in the JSON output.\n"
                initial_prompt += "IMPORTANT: When you fly from city A to city B on day X, that day counts for BOTH cities. For example:\n"
                initial_prompt += "- If you stay in Venice from Day 1-3 and fly to Vienna on Day 3, then:\n"
                initial_prompt += "  - Venice: Day 1-3 (3 days)\n"
                initial_prompt += "  - Vienna: Day 3-6 (4 days, including the flight day)\n"
                initial_prompt += "- The flight day (Day 3) is counted for both Venice and Vienna.\n"
                initial_prompt += "- Do NOT create separate flight entries in the JSON.\n"
            elif task == "meeting":
                initial_prompt += "Your output should be a JSON-formatted dictionary with an 'itinerary' key containing a list of meeting entries.\n"
                initial_prompt += "Each meeting entry should have the following format:\n"
                initial_prompt += '{"action": "meet", "person": "<person_name>", "start_time": "<HH:MM>", "end_time": "<HH:MM>"}\n'
                initial_prompt += "The time should be in 24-hour format. For example:\n"
                initial_prompt += '{"itinerary": [{"action": "meet", "person": "David", "start_time": "13:00", "end_time": "14:00"}]}\n'
            elif task == "zebralogic":
                golden_plan = example.get("golden_plan", {})
                golden_headers = golden_plan.get("header", [])
                header_placeholder = json.dumps(golden_headers)
                
                initial_prompt += "Your output should be a JSON-formatted dictionary with the following EXACT structure:\n"
                initial_prompt += "{\n"
                initial_prompt += '  "solution": {\n'
                initial_prompt += f'    "header": {header_placeholder},\n'
                initial_prompt += '    "rows": [\n'
                initial_prompt += '      ["1", VALUE_FOR_HEADER1, VALUE_FOR_HEADER2, ...],\n'
                initial_prompt += '      ["2", VALUE_FOR_HEADER1, VALUE_FOR_HEADER2, ...]\n'
                initial_prompt += '    ]\n'
                initial_prompt += "  }\n"
                initial_prompt += "}\n\n"
                initial_prompt += "Important Requirements:\n"
                initial_prompt += f"- The 'header' field MUST use exactly these attribute names: {header_placeholder}\n"
                initial_prompt += "- Maintain the exact order of houses (1, 2, 3...)\n"
                initial_prompt += "- Include all attributes in each row\n"
                initial_prompt += "- The output must be valid JSON that can be parsed by Python's json module\n"
            
            initial_prompt += "Write a Python program that solves it using the Z3 solver. Always surround your final code with ```python\nYOUR_CODE\n```.\n"
            
            # For Qwen2.5 models, add explicit reasoning instructions to match Python token pass format
            if "qwen" in model.lower() and ("2.5" in model.lower() or "reasoning" in model.lower()):
                # Add reasoning instructions before the final code instruction
                reasoning_instruction = (
                    "\n\nPlease reason step by step about how to solve this problem. "
                    "Enclose your reasoning process within <reasoning> and </reasoning> tags, then provide your solution code. "
                    "Use this format:\n\n<reasoning>\nYour step-by-step reasoning here...\n</reasoning>\n\nThen provide your code solution.\n\n"
                )
                # Insert before "Write a Python program" or "Always surround" - whichever comes first
                if "Write a Python program" in initial_prompt:
                    initial_prompt = initial_prompt.replace(
                        "Write a Python program",
                        reasoning_instruction + "Write a Python program",
                        1
                    )
                elif "Always surround your final code" in initial_prompt:
                    initial_prompt = initial_prompt.replace(
                        "Always surround your final code",
                        reasoning_instruction + "Always surround your final code",
                        1
                    )
                else:
                    # Fallback: append at the end
                    initial_prompt = initial_prompt.rstrip() + reasoning_instruction
                logging.info(f"[{example_id}] Added reasoning instructions for {model}")
            
            current_prompt = initial_prompt
            prompt_prep_time = time.time() - prompt_prep_start
            logging.info(f"[{example_id}] Prompt prepared - {prompt_prep_time:.2f}s")
            
            # Extract gold answer for evaluation
            gold_extract_start = time.time()
            gold = example.get("golden_plan", "")
            if isinstance(gold, list):
                gold = "\n".join(gold)
            logging.info(f"[{example_id}] Raw gold answer: {gold}")
            try:
                if task == "zebralogic":
                    gold_formatted = parse_zebralogic_golden(gold)
                else:
                    gold_formatted = extract_answer_basic(gold, task)
                logging.info(f"[{example_id}] Extracted gold: {gold_formatted}")
            except Exception as e:
                logging.error(f"[{example_id}] Failed to extract gold: {e}")
                gold_formatted = {}
            gold_extract_time = time.time() - gold_extract_start
            logging.info(f"[{example_id}] Gold extraction completed - {gold_extract_time:.2f}s")
            
            for pass_num in range(1, max_passes + 1):
                pass_start_time = time.time()
                logging.info(f"[{example_id}] Starting pass {pass_num}")
                
                # Create output directory for this pass
                dir_create_start = time.time()
                pass_output_dir = f"{output_dir}/{pass_num}_pass"
                os.makedirs(pass_output_dir, exist_ok=True)
                dir_create_time = time.time() - dir_create_start
                
                # Get response from model with rate limiting
                api_call_start = time.time()
                retry_count = 0
                max_retries = 3
                while retry_count < max_retries:
                    try:
                        logging.info(f"[{example_id}] Making API call (attempt {retry_count + 1})")
                        response_txt = await run_model_with_rate_limit(ai, current_prompt, rate_limiter)
                        logging.info(f"[{example_id}] API call successful")
                        break
                    except Exception as e:
                        retry_count += 1
                        logging.warning(f"[{example_id}] API error in pass {pass_num} (attempt {retry_count}): {e}")
                        if retry_count >= max_retries:
                            logging.error(f"[{example_id}] Max retries reached, giving up")
                            # Save error evaluation result
                            error_eval_result = {
                                "has_execution_error": True,
                                "execution_output": f"Max API retries ({max_retries}) reached in pass {pass_num}",
                                "pred": {},
                                "gold": {},
                                "status": "API retry limit exceeded",
                                "violated_constraint": {},
                                "is_exact_match": False,
                                "constraints_satisfied": False,
                                "pass_number": pass_num
                            }
                            with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                                json.dump(error_eval_result, f, indent=4)
                            return
                        await asyncio.sleep(5)
                        try:
                            ai = initialize_model(model, keys)
                            logging.info(f"[{example_id}] Model reinitialized after error")
                        except Exception as init_error:
                            logging.error(f"[{example_id}] Failed to reinitialize model: {str(init_error)}")
                            # Save error evaluation result
                            error_eval_result = {
                                "has_execution_error": True,
                                "execution_output": f"Model reinitialization failed: {str(init_error)}",
                                "pred": {},
                                "gold": {},
                                "status": "Model reinitialization error",
                                "violated_constraint": {},
                                "is_exact_match": False,
                                "constraints_satisfied": False,
                                "pass_number": pass_num
                            }
                            with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                                json.dump(error_eval_result, f, indent=4)
                            return
                
                api_call_time = time.time() - api_call_start
                logging.info(f"[{example_id}] Pass {pass_num} API call completed - {api_call_time:.2f}s")
                
                # Extract reasoning content and tokens for Qwen models (and other HuggingFace models)
                reasoning_content = ""
                reasoning_tokens = 0
                if "qwen" in model.lower() or "huggingface" in str(type(ai)).lower():
                    reasoning_content, reasoning_tokens = extract_reasoning(response_txt, model)
                    logging.info(f"[{example_id}] Pass {pass_num} reasoning content extracted: {len(reasoning_content)} characters")
                    if reasoning_content:
                        logging.info(f"[{example_id}] Pass {pass_num} first 200 chars of reasoning: {reasoning_content[:200]}...")
                
                # Count total tokens (approximate)
                total_tokens = count_tokens(response_txt) if response_txt else 0
                
                # Add to conversation history (matching Python token pass format)
                conversation_history.append({"role": "user", "content": current_prompt})
                conversation_history.append({
                    "role": "assistant",
                    "content": response_txt,
                    "reasoning_content": reasoning_content,
                    "reasoning_tokens": reasoning_tokens,
                    "total_tokens": total_tokens
                })
                
                # Save conversation
                save_start = time.time()
                with open(f"{pass_output_dir}/conversation.json", "w") as f:
                    json.dump(conversation_history, f, indent=4)
                
                # Extract and save code using smart extraction
                code_extract_start = time.time()
                generated_code = smart_extract_code(response_txt)
                if not generated_code:
                    logging.error(f"[{example_id}] No code found in model response")
                    # Save error evaluation result (with reasoning fields)
                    error_eval_result = {
                        "has_execution_error": True,
                        "execution_output": "No code found in model response",
                        "pred": {},
                        "gold": gold_formatted,
                        "status": "No code extracted",
                        "violated_constraint": {},
                        "is_exact_match": False,
                        "constraints_satisfied": False,
                        "pass_number": pass_num,
                        "timing": {
                            "api_call_time": api_call_time,
                            "execution_time": 0,
                            "total_tokens": total_tokens,
                            "reasoning_tokens": reasoning_tokens
                        },
                        "reasoning_content": reasoning_content
                    }
                    with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                        json.dump(error_eval_result, f, indent=4)
                    
                    # Also save reasoning content separately if it exists
                    if reasoning_content:
                        with open(f"{pass_output_dir}/reasoning.txt", "w") as f:
                            f.write(reasoning_content)
                    
                    # Save the full raw response
                    if response_txt:
                        with open(f"{pass_output_dir}/full_response.txt", "w") as f:
                            f.write(response_txt)
                    
                    # Prepare feedback for next iteration (include reasoning instructions for Qwen)
                    feedback_prompt = f"Code extraction from the previous response failed. Please provide a complete Python solution using the Z3 solver. Make sure to surround your final code with ```python\nYOUR_CODE\n```.\n\nOriginal problem:\n{example['prompt_0shot']}"
                    
                    # Add reasoning instructions for Qwen models in feedback prompts too
                    if "qwen" in model.lower() and ("2.5" in model.lower() or "reasoning" in model.lower()):
                        reasoning_instruction = (
                            "\n\nPlease reason step by step about how to solve this problem. "
                            "Enclose your reasoning process within <reasoning> and </reasoning> tags, then provide your solution code. "
                            "Use this format:\n\n<reasoning>\nYour step-by-step reasoning here...\n</reasoning>\n\nThen provide your code solution.\n\n"
                        )
                        feedback_prompt = feedback_prompt.replace(
                            "Make sure to surround your final code",
                            reasoning_instruction + "Make sure to surround your final code",
                            1
                        )
                    
                    current_prompt = feedback_prompt
                    continue
                    
                code_path = f"{pass_output_dir}/solution.py"
                with open(code_path, "w") as f:
                    f.write(generated_code)
                code_extract_time = time.time() - code_extract_start
                logging.info(f"[{example_id}] Pass {pass_num} code extracted and saved - {code_extract_time:.2f}s")
                
                # Execute code
                execution_start = time.time()
                execution_output = execute_python_code(code_path)
                execution_time = time.time() - execution_start
                logging.info(f"[{example_id}] Pass {pass_num} code execution - {execution_time:.2f}s")
                
                with open(f"{pass_output_dir}/output.out", "w") as f:
                    f.write(execution_output)
                
                # Extract structured answer from execution output using smart extraction
                pred_extract_start = time.time()
                try:
                    if task == "zebralogic":
                        pred_formatted = parse_zebralogic_output(execution_output)
                    else:
                        pred_formatted = smart_extract_execution_result(execution_output, task)
                    logging.info(f"[{example_id}] Pass {pass_num} extracted prediction: {pred_formatted}")
                except Exception as e:
                    logging.error(f"[{example_id}] Pass {pass_num} failed to extract prediction: {str(e)}")
                    pred_formatted = {}
                
                # Enhanced error handling for different execution scenarios
                # Compute is_exact_match
                execution_error = None
                no_plan_found = False
                if isinstance(pred_formatted, dict):
                    if "error" in pred_formatted:
                        # Check if it's actually a no-plan case (empty output or malformed_output)
                        if pred_formatted["error"] == "malformed_output" and (not execution_output or execution_output.strip() == ""):
                            no_plan_found = True
                        else:
                            execution_error = pred_formatted["error"]
                    elif "no_plan" in pred_formatted:
                        no_plan_found = True
                # Also check for empty execution output directly
                if not execution_output or execution_output.strip() == "":
                    no_plan_found = True
                    execution_error = None

                is_exact_match = False
                if not execution_error and not no_plan_found:
                    if task == "trip":
                        normalized_pred = normalize_trip_itinerary(pred_formatted)
                        normalized_gold = normalize_trip_itinerary(gold_formatted)
                        is_exact_match = normalized_pred == normalized_gold
                    else:
                        is_exact_match = pred_formatted == gold_formatted
                    
                    # Evaluate constraints
                    eval_func = eval_functions[task]
                    constraints_satisfied, violated_constraints = eval_func(constraints, pred_formatted)

                # Save evaluation result (with reasoning fields matching Python token pass format)
                eval_result = {
                    "has_execution_error": bool(execution_error),
                    "execution_output": execution_output,
                    "pred": pred_formatted,
                    "gold": gold_formatted,
                    "status": ("Correct" if constraints_satisfied else ("No plan found" if no_plan_found else "Wrong plan")),
                    "violated_constraint": violated_constraints,
                    "is_exact_match": is_exact_match,
                    "constraints_satisfied": constraints_satisfied,
                    "pass_number": pass_num,
                    "timing": {
                        "api_call_time": api_call_time,
                        "execution_time": execution_time,
                        "total_tokens": total_tokens,
                        "reasoning_tokens": reasoning_tokens
                    },
                    "reasoning_content": reasoning_content
                }
                with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                    json.dump(eval_result, f, indent=4)
                
                # Also save reasoning content separately if it exists (matching Python token pass format)
                if reasoning_content:
                    with open(f"{pass_output_dir}/reasoning.txt", "w") as f:
                        f.write(reasoning_content)
                
                # Save the full raw response (matching Python token pass format)
                if response_txt:
                    with open(f"{pass_output_dir}/full_response.txt", "w") as f:
                        f.write(response_txt)
                
                # Check for success conditions
                if constraints_satisfied:
                    logging.info(f"[{example_id}] SUCCESS! Solved in pass {pass_num}")
                    return
                
                # Prepare enhanced feedback for next iteration based on different scenarios
                if execution_error:
                    # Scenario 3: Execution error - provide error message as feedback
                    logging.info(f"[{example_id}] Pass {pass_num} execution error, preparing error feedback")
                    current_prompt = f"The previous Z3 solution returned an error: {execution_output}\n\nPlease revise your Z3 program to fix this error. The error suggests there may be an issue with the Z3 code.\n\nMake sure to surround your final code with ```python\nYOUR_CODE\n```."
                
                elif no_plan_found:
                    # Scenario 4: No plan found - suggest adjusting solution
                    logging.info(f"[{example_id}] Pass {pass_num} no plan found, preparing no-plan feedback")
                    no_plan_reason = pred_formatted.get('no_plan', 'Unknown reason')
                    current_prompt = f"The previous Z3 solution failed to find a plan.\n\nPlease adjust your Z3 program to find a solution.\n\nMake sure to surround your final code with ```python\nYOUR_CODE\n```."
                
                else:
                    # Scenario 5: Plan found but violates constraints - provide plan details with constraint violations
                    logging.info(f"[{example_id}] Pass {pass_num} plan found but violates constraints, preparing constraint feedback")
                    plan_summary = f"Plan found: {pred_formatted}"
                    feedback_func = feedback_functions[task]
                    constraint_feedback = feedback_func(violated_constraints)
                    current_prompt = f"The previous solution produced the following plan:\n{plan_summary}\n\n{constraint_feedback}\n\nPlease revise your Z3 program to find a valid solution that satisfies all constraints.\n\nMake sure to surround your final code with ```python\nYOUR_CODE\n```."
                
                # Add reasoning instructions for Qwen models in feedback prompts too
                if "qwen" in model.lower() and ("2.5" in model.lower() or "reasoning" in model.lower()):
                    reasoning_instruction = (
                        "\n\nPlease reason step by step about how to solve this problem. "
                        "Enclose your reasoning process within <reasoning> and </reasoning> tags, then provide your solution code. "
                        "Use this format:\n\n<reasoning>\nYour step-by-step reasoning here...\n</reasoning>\n\nThen provide your code solution.\n\n"
                    )
                    if "Make sure to surround your final code" in current_prompt:
                        current_prompt = current_prompt.replace(
                            "Make sure to surround your final code",
                            reasoning_instruction + "Make sure to surround your final code",
                            1
                        )
                    else:
                        # Fallback: append at the end
                        current_prompt = current_prompt.rstrip() + reasoning_instruction
            
            logging.warning(f"[{example_id}] FAILED to solve within {max_passes} passes")
            
            # Save final evaluation result even if we failed to solve
            if 'pred_formatted' in locals() and 'gold_formatted' in locals():
                # Determine the correct status based on what happened in the last pass
                if execution_output == "No code found in model response":
                    final_status = "No code extracted"
                elif execution_error:
                    final_status = f"Execution error: {execution_error}"
                elif no_plan_found:
                    final_status = f"No plan found: {pred_formatted.get('no_plan', 'Unknown reason')}"
                elif not constraints_satisfied:
                    final_status = "Wrong plan"
                else:
                    final_status = "Failed to solve within max passes"
                
                # Get reasoning and timing info from last pass (if available)
                last_reasoning_content = reasoning_content if 'reasoning_content' in locals() else ""
                last_reasoning_tokens = reasoning_tokens if 'reasoning_tokens' in locals() else 0
                last_total_tokens = total_tokens if 'total_tokens' in locals() else 0
                last_execution_time = execution_time if 'execution_time' in locals() else 0
                last_api_call_time = api_call_time if 'api_call_time' in locals() else 0
                
                final_eval_result = {
                    "has_execution_error": bool(execution_error),
                    "execution_output": execution_output,
                    "pred": pred_formatted,
                    "gold": gold_formatted,
                    "status": final_status,
                    "violated_constraint": violated_constraints,
                    "is_exact_match": is_exact_match,
                    "constraints_satisfied": constraints_satisfied,
                    "pass_number": pass_num,
                    "timing": {
                        "api_call_time": last_api_call_time,
                        "execution_time": last_execution_time,
                        "total_tokens": last_total_tokens,
                        "reasoning_tokens": last_reasoning_tokens
                    },
                    "reasoning_content": last_reasoning_content
                }
                with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                    json.dump(final_eval_result, f, indent=4)
                
                # Also save reasoning content separately if it exists
                if last_reasoning_content:
                    with open(f"{pass_output_dir}/reasoning.txt", "w") as f:
                        f.write(last_reasoning_content)
                
                # Save the full raw response if available
                if 'response_txt' in locals() and response_txt:
                    with open(f"{pass_output_dir}/full_response.txt", "w") as f:
                        f.write(response_txt)
                
                logging.info(f"[{example_id}] Saved final evaluation result from pass {pass_num} with status: {final_status}")
            
            return
            
        except Exception as e:
            logging.error(f"[{example_id}] Unexpected error: {str(e)}")
            # Save error evaluation result
            try:
                error_eval_result = {
                    "has_execution_error": True,
                    "execution_output": f"Unexpected error: {str(e)}",
                    "pred": {},
                    "gold": {},
                    "status": "Unexpected error",
                    "violated_constraint": {},
                    "is_exact_match": False,
                    "constraints_satisfied": False,
                    "pass_number": 0
                }
                # Try to save to first pass directory, create if needed
                first_pass_dir = f"{output_dir}/1_pass"
                os.makedirs(first_pass_dir, exist_ok=True)
                with open(f"{first_pass_dir}/evaluation.json", "w") as f:
                    json.dump(error_eval_result, f, indent=4)
                logging.info(f"[{example_id}] Saved error evaluation result")
            except Exception as save_error:
                logging.error(f"[{example_id}] Failed to save error evaluation: {str(save_error)}")
            return 

async def main():
    """Main function to run the enhanced iterative SMT refinement"""
    args = parse_args()
    
    # Set up logging
    logging.info(f"Starting enhanced iterative SMT refinement")
    logging.info(f"Model: {args.model}")
    logging.info(f"Task: {args.task}")
    logging.info(f"Max passes: {args.max_passes}")
    logging.info(f"Max concurrent: {args.max_concurrent}")
    logging.info(f"Rate limit: {args.rate_limit} requests/minute")
    
    # Load data - handle ZebraLogic differently
    if args.task == "zebralogic":
        data_path = f"../data/zebralogic_sample_100.json"
        try:
            with open(data_path, 'r') as f:
                data = json.load(f)
            # For ZebraLogic, we'll use the golden plan as constraints
            constraints_data = {}
            for example_id, example in data.items():
                constraints_data[example_id] = {
                    "constraints": {
                        "golden_plan": example["golden_plan"]
                    }
                }
            logging.info(f"Loaded {len(data)} ZebraLogic examples from {data_path}")
        except FileNotFoundError as e:
            logging.error(f"ZebraLogic data file not found: {e}")
            return
    else:
        # Normal task loading
        data_path = f"../data/{task_name_map[args.task]}_100.json"
        constraints_path = f"../data/{task_name_map[args.task]}_100_constraints.json"
        try:
            with open(data_path, 'r') as f:
                data = json.load(f)
            with open(constraints_path, 'r') as f:
                constraints_data = json.load(f)
            logging.info(f"Loaded {len(data)} examples from {data_path}")
            logging.info(f"Loaded constraints from {constraints_path}")
        except FileNotFoundError as e:
            logging.error(f"Data file not found: {e}")
            return
    
    # Determine which examples to process
    if args.examples:
        # Process specific examples
        example_numbers = [int(x.strip()) for x in args.examples.split(',')]
        examples_to_process = []
        for num in example_numbers:
            example_id = f"{task_name_map[args.task]}_example_{num}"
            if example_id in data:
                examples_to_process.append((example_id, data[example_id]))
            else:
                logging.warning(f"Example {example_id} not found in data, skipping")
    elif args.start is not None or args.end is not None:
        # Filter examples by start/end range - same approach as parallel version
        logging.info(f"Filtering examples: start={args.start}, end={args.end}")
        # Convert examples dict to list of (example_id, example) tuples and slice
        examples_list = list(data.items())
        start_idx = args.start if args.start is not None else 0
        end_idx = args.end if args.end is not None else len(examples_list)
        
        # Slice the examples list
        filtered_examples_list = examples_list[start_idx:end_idx]
        examples_to_process = filtered_examples_list
        logging.info(f"Filtered to {len(examples_to_process)} examples (indices {start_idx} to {end_idx-1})")
    else:
        # Process all examples
        examples_to_process = list(data.items())
    
    logging.info(f"Processing {len(examples_to_process)} examples")
    
    # Clear output directories if fresh flag is set
    if args.fresh:
        output_base = f"../output/SMT/{args.model}/{args.task}/token_pass"
        if os.path.exists(output_base):
            shutil.rmtree(output_base)
            logging.info(f"Cleared output directory: {output_base}")
    
    # Set up rate limiting and concurrency
    rate_limiter = RateLimiter(args.rate_limit / 60.0)  # Convert to requests per second
    semaphore = asyncio.Semaphore(args.max_concurrent)
    
    # Process examples
    start_time = time.time()
    tasks = []
    
    for example_id, example in examples_to_process:
        # Check if example should be skipped or needs to be redone (output files are source of truth)
        if not args.fresh:
            # PRIMARY CHECK: Check if output files exist and are complete
            if check_example_complete(args.task, example_id, args.model):
                logging.info(f"[SKIP] {args.task} example {example_id} - already has complete output files, skipping")
                continue
            
            # SECONDARY CHECK: If output folder exists but is incomplete, clear it
            output_path = os.path.abspath(f"../output/SMT/{args.model}/{args.task}/token_pass/{example_id}")
            if os.path.exists(output_path):
                # Folder exists but check_example_complete returned False - it's incomplete
                logging.info(f"[CLEAR] Detected incomplete/interrupted output for {args.task} example {example_id} at {output_path}, clearing folder and restarting...")
                clear_incomplete_example(args.task, example_id, args.model)
        
        constraints = constraints_data.get(example_id, {}).get("constraints", {})
        task = asyncio.create_task(
            process_single_example(
                example_id, example, constraints, args.model, 
                args.max_passes, rate_limiter, semaphore, args.task, args
            )
        )
        tasks.append(task)
    
    # Wait for all tasks to complete
    await asyncio.gather(*tasks, return_exceptions=True)
    
    total_time = time.time() - start_time
    logging.info(f"Completed processing {len(examples_to_process)} examples in {total_time:.2f} seconds")
    logging.info(f"Average time per example: {total_time / len(examples_to_process):.2f} seconds")

if __name__ == "__main__":
    asyncio.run(main())
