"""
Parallel Iterative Plan Refinement with Constraint Feedback

This script implements an iterative refinement process for solving planning problems (calendar, meeting, trip)
by generating plans directly using LLMs, evaluating constraints, and providing feedback for improvement.

Features:
1. Generates plans directly using various LLM models (GPT, DeepSeek, etc.)
2. Uses prompts from force JSON files (calendar, meeting, trip)
3. Evaluates the solution against domain-specific constraints
4. Provides iterative feedback for constraint violations
5. Saves conversation history, plans, and evaluation results for each pass
6. Parallel processing with rate limiting for efficiency

Directory structure for outputs:
../output/Plan/{model_name}/{task}/n_pass/{example_id}/{pass_number}_pass/
  - conversation.json: Full conversation history
  - plan.json: Generated plan
  - evaluation.json: Constraint evaluation results

Usage:
python iterative_plan_refinement_parallel.py --task calendar --model gpt-4o-mini --start 0 --end 5
python iterative_plan_refinement_parallel.py --task all --model DeepSeek-V3 gpt-4o-mini --max_passes 3
"""

import argparse
import json
import os
import asyncio
import re
import time
from datetime import datetime
from kani import Kani, chat_in_terminal
from kani.engines.huggingface import HuggingEngine
from kani.engines.openai import OpenAIEngine
import concurrent.futures
from typing import List, Dict, Any, Tuple
import logging
import shutil
from openai import OpenAI

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('iterative_plan_refinement.log'),
        logging.StreamHandler()
    ]
)

def parse_args():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(description="Run iterative plan refinement with parallel processing")
    parser.add_argument("--model", type=str, required=True, help="Model to use (e.g., 'DeepSeek-R1')")
    parser.add_argument("--task", type=str, required=True, choices=["calendar", "trip", "meeting"], help="Task type")
    parser.add_argument("--max_passes", type=int, default=5, help="Maximum number of refinement passes")
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

# Load API keys
try:
    with open("../scheduling_key.json") as f:
        keys = json.load(f)
except FileNotFoundError:
    logging.error("scheduling_key.json not found. Please create this file with your API keys.")
    exit(1)

def initialize_model(model_name, keys):
    """Initializes the Kani AI model based on the model name."""
    if model_name.startswith("gpt") or model_name.startswith("o"):
        if model_name == "o3-mini":
            model_name = "o3-mini-2025-01-31"
        elif model_name == "gpt-4o-mini":
            model_name = "gpt-4o-mini-2024-07-18"
        engine = OpenAIEngine(keys["openai"], model=model_name, max_context_size=20000)
    elif model_name == "DeepSeek-R1":
        engine = OpenAIEngine(keys["deepseek"], model="deepseek-reasoner", api_base="https://api.deepseek.com", max_context_size=20000)
    elif model_name == "DeepSeek-V3":
        engine = OpenAIEngine(keys["deepseek"], model="deepseek-chat", api_base="https://api.deepseek.com", max_context_size=20000)
    else:
        engine = HuggingEngine(model_id=model_name)

    ai = Kani(engine, system_prompt="")
    return ai

# JSON schemas for different tasks
JSON_SCHEMAS = {
    "calendar": {
        "name": "time_range_schema",
        "schema": {
            "type": "object",
            "properties": {
                "time_range": {
                    "type": "string",
                    "pattern": "^\\{\\d{1,2}:\\d{2}:\\d{1,2}:\\d{2}\\}$"
                },
                "day": {
                    "type": "string",
                }
            },
            "required": ["time_range", "day"],
            "em": ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
        }
    },
    "meeting": {
        "name": "meeting_plan_schema",
        "schema": {
            "type": "object",
            "properties": {
                "itinerary": {
                    "type": "array",
                    "items": {
                        "type": "object",
                        "properties": {
                            "action": {"type": "string", "enum": ["meet"]},
                            "location": {"type": "string"},
                            "person": {"type": "string"},
                            "start_time": {"type": "string"},
                            "end_time": {"type": "string"}
                        },
                        "required": ["action", "location", "person", "start_time", "end_time"]
                    }
                }
            },
            "required": ["itinerary"]
        }
    },
    "trip": {
        "name": "trip_plan_schema",
        "schema": {
            "type": "object",
            "properties": {
                "itinerary": {
                    "type": "array",
                    "items": {
                        "anyOf": [
                            {
                                "type": "object",
                                "properties": {
                                    "day_range": {"type": "string", "pattern": "^Day \\d+-\\d+$"},
                                    "place": {"type": "string"}
                                },
                                "required": ["day_range", "place"]
                            },
                            {
                                "type": "object",
                                "properties": {
                                    "flying": {"type": "string", "pattern": "^Day \\d+-\\d+$"},
                                    "from": {"type": "string"},
                                    "to": {"type": "string"}
                                },
                                "required": ["flying", "from", "to"]
                            }
                        ]
                    }
                }
            },
            "required": ["itinerary"]
        }
    }
}

def get_task_prompt(task, example):
    """Get the appropriate prompt for the task type"""
    if task == "calendar":
        return example['prompt_0shot']
    elif task == "meeting":
        return example['prompt_0shot']
    elif task == "trip":
        return example['prompt_0shot']
    else:
        raise ValueError(f"Unknown task type: {task}")

def add_json_formatting_instruction(prompt, task):
    """Add JSON formatting instruction to the prompt based on task type"""
    if task == "calendar":
        return prompt + "\n\nPlease output the proposed time in the following JSON format:\n{\"time_range\": \"{HH:MM:HH:MM}\", \"day\": \"<DAY>\"}. For example, if the proposed time is Tuesday, 14:30 to 15:30, the output should be:\n{\"time_range\": \"{14:30:15:30}\", \"day\": \"Tuesday\"}."
    elif task == "meeting":
        return prompt + "\n\nPlease output the meeting schedule in the following JSON format:\n{\"itinerary\": [{\"action\": \"meet\", \"person\": \"<PERSON_NAME>\", \"start_time\": \"<HH:MM>\", \"end_time\": \"<HH:MM>\"}]}. Make sure to include the person's name for each meeting."
    elif task == "trip":
        return prompt + "\n\nPlease output the trip plan in the following JSON format:\n{\"itinerary\": [{\"day_range\": \"Day X-Y\", \"place\": \"<CITY>\"}]}. Include all city visits with their day ranges. Do not include separate flight entries in the JSON output.\n\nIMPORTANT: When you fly from city A to city B on day X, that day counts for BOTH cities. For example:\n- If you stay in Venice from Day 1-3 and fly to Vienna on Day 3, then:\n  - Venice: Day 1-3 (3 days)\n  - Vienna: Day 3-6 (4 days, including the flight day)\n- The flight day (Day 3) is counted for both Venice and Vienna.\n- Do NOT create separate flight entries in the JSON."
    else:
        return prompt

def evaluate_calendar(constraints, pred_dict):
    """Evaluate calendar constraints comprehensively (flat dict, not nested)"""
    # Check for missing fields
    if not pred_dict or "day" not in pred_dict or "time_range" not in pred_dict:
        return False, {"missing_fields": True}

    pred_day = pred_dict["day"]
    time_range = pred_dict["time_range"]
    
    # Check for None values
    if pred_day is None or time_range is None:
        return False, {"null_fields": True}
    
    # Parse time range
    try:
        time_range = time_range.replace("{", "").replace("}", "")
        parts = time_range.split(":")
        if len(parts) == 4:
            # Format: HH:MM:HH:MM
            start_time = float(parts[0]) + float(parts[1]) / 60
            end_time = float(parts[2]) + float(parts[3]) / 60
        else:
            return False, {"invalid_time_range_format": time_range}
    except Exception as e:
        return False, {"unparsable_time_range": time_range}

    # Check meeting duration
    meeting_duration = constraints.get("meeting_duration")
    if meeting_duration is None:
        meeting_duration = 1.0  # Default fallback
    actual_duration = end_time - start_time
    if abs(actual_duration - meeting_duration) > 1e-3:
        return False, {"meeting_duration": {"required": meeting_duration, "actual": actual_duration}}

    # Check disallowed ranges
    for rng in constraints.get("disallowed_ranges", []):
        if rng["day"] == pred_day:
            rng_start = rng["start"]
            rng_end = rng["end"]
            # If any overlap
            if not (end_time <= rng_start or start_time >= rng_end):
                return False, {"disallowed_range": rng}

    return True, {}

def evaluate_meeting(constraints, pred_dict):
    """Evaluate meeting constraints comprehensively (flat dict, not nested)"""
    from datetime import datetime
    
    # Check for missing itinerary
    if not pred_dict or "itinerary" not in pred_dict:
        return False, {"missing_itinerary": True}
    
    itinerary = pred_dict["itinerary"]
    if not isinstance(itinerary, list):
        return False, {"invalid_itinerary": True}
    
    # Check number of people to meet (use num_people_to_meet if available, otherwise check people_to_meet)
    num_people_to_meet = constraints.get("num_people_to_meet", 0)
    met_people = set()
    
    for m in itinerary:
        if "person" not in m or "start_time" not in m or "end_time" not in m:
            return False, {"missing_meeting_fields": m}
        
        person = m["person"]
        # Require person name to be provided
        if not person or person == "Unknown":
            return False, {"missing_person_name": "Person name must be provided for each meeting"}
        
        met_people.add(person)
    
    # Check if we meet enough people
    if num_people_to_meet > 0 and len(met_people) < num_people_to_meet:
        return False, {"num_people_to_meet": num_people_to_meet}
    
    # If no num_people_to_meet constraint, fall back to checking people_to_meet
    if num_people_to_meet == 0:
        people_to_meet = constraints.get("people_to_meet", [])
        people_names = set(p["name"] for p in people_to_meet)
        if people_names and not people_names.issubset(met_people):
            return False, {"unmet_people": list(people_names - met_people)}
    
    return True, {}

def evaluate_trip(constraints, pred_dict):
    """Evaluate trip constraints comprehensively (flat dict, not nested)"""
    # Check for missing itinerary
    if not pred_dict or "itinerary" not in pred_dict:
        return False, {"missing_itinerary": True}
    
    itinerary = pred_dict["itinerary"]
    if not isinstance(itinerary, list):
        return False, {"invalid_itinerary": True}
    
    # Parse itinerary segments
    segments = []
    for seg in itinerary:
        if "day_range" not in seg or "place" not in seg:
            return False, {"missing_segment_fields": seg}
        
        # Parse day range
        day_range = seg["day_range"]
        if not day_range.startswith("Day "):
            return False, {"invalid_day_range_format": day_range}
        dr = day_range.replace("Day ", "")
        if "-" in dr:
            start_s, end_s = dr.split("-")
        else:
            start_s, end_s = [dr, dr]
        try:
            start, end = int(start_s), int(end_s)
        except ValueError:
            return False, {"unparsable_day_range": day_range}
        segments.append({"place": seg["place"], "start": start, "end": end})
    
    # Validate trip starts on day 1 and ends on the correct day
    trip_length = constraints.get("trip_length")
    if trip_length is not None:
        if not segments or segments[0]["start"] != 1 or segments[-1]["end"] != trip_length:
            return False, {"trip_length": {"required": trip_length, "actual": "invalid_start_end"}}
        
        # Check for gaps or overlaps between consecutive segments
        for a, b in zip(segments, segments[1:]):
            if a["end"] != b["start"]:
                return False, {"gap_or_overlap": {"between": f"Day {a['end']} and Day {b['start']}"}}
    
    # Check stay_days (convert from city_length format for consistency with Python refinement)
    # Convert city_length format to stay_days format
    city_length = constraints.get("city_length", [])
    stay_days = {}
    for city_req in city_length:
        stay_days[city_req["city"]] = city_req["days"]
    
    for seg in segments:
        required = stay_days.get(seg["place"])
        if required is not None:
            actual = seg["end"] - seg["start"] + 1
            if actual != required:
                return False, {"stay_days": {seg["place"]: required}}
    
    # Check flight constraints
    allowed_flights = [(d["from"], d["to"]) for d in constraints.get("direct_flights", [])]
    for a, b in zip(segments, segments[1:]):
        pair = (a["place"], b["place"])
        if pair not in allowed_flights:
            return False, {"flight": {"from": a["place"], "to": b["place"]}}
    
    return True, {}

def normalize_trip_itinerary(itinerary):
    """Normalize trip itinerary for exact match comparison"""
    if not itinerary or "itinerary" not in itinerary:
        return {}
    
    normalized = {"itinerary": []}
    for item in itinerary["itinerary"]:
        if "day_range" in item and "place" in item:
            normalized["itinerary"].append({
                "day_range": item["day_range"],
                "place": item["place"]
            })
        elif "flying" in item and "from" in item and "to" in item:
            normalized["itinerary"].append({
                "flying": item["flying"],
                "from": item["from"],
                "to": item["to"]
            })
    
    return normalized

def extract_answer_from_text(text, task):
    """Extract structured answer from text response"""
    import re
    
    if task == "calendar":
        # First try to extract JSON from the response
        json_pattern = r'```json\s*(\{.*?\})\s*```'
        json_match = re.search(json_pattern, text, re.DOTALL | re.IGNORECASE)
        if json_match:
            try:
                json_str = json_match.group(1)
                result = json.loads(json_str)
                if "time_range" in result and "day" in result:
                    return result
            except json.JSONDecodeError:
                pass
        
        # Try to find JSON without code blocks
        json_pattern2 = r'\{[^}]*"time_range"[^}]*"day"[^}]*\}'
        json_match2 = re.search(json_pattern2, text)
        if json_match2:
            try:
                return json.loads(json_match2.group(0))
            except json.JSONDecodeError:
                pass
        
        # Look for time range pattern in the format "Monday, 13:30 - 14:30"
        time_pattern = r'(Monday|Tuesday|Wednesday|Thursday|Friday|Saturday|Sunday),?\s*(\d{1,2}:\d{2})\s*-\s*(\d{1,2}:\d{2})'
        match = re.search(time_pattern, text, re.IGNORECASE)
        
        if match:
            day = match.group(1)
            start_time = match.group(2)
            end_time = match.group(3)
            
            # Convert to the expected format {HH:MM:HH:MM}
            time_range = f"{{{start_time}:{end_time}}}"
            
            return {
                "day": day,
                "time_range": time_range
            }
        
        return None
    
    elif task == "meeting":
        # Use LLM-based extraction for meetings (following SMT/Python approach)
        import os
        
        # Try to get OpenAI API key
        openai_key = None
        try:
            # Try to load from scheduling_key.json
            with open("../../scheduling_key.json") as f:
                key_data = json.load(f)
                openai_key = key_data.get("openai")
        except (FileNotFoundError, KeyError):
            # Try environment variable
            openai_key = os.getenv("OPENAI_API_KEY")
        
        if not openai_key:
            print("Warning: Could not find OpenAI API key for answer extraction")
            return None
        
        try:
            client = OpenAI(api_key=openai_key)
        except Exception as e:
            print(f"Warning: Could not initialize OpenAI client for answer extraction: {e}")
            return None
        
        # Define extraction prompt for meetings
        prompt = f"Given the following meeting schedule:\n{text}\nExtract the time and the person of each meeting in a JSON format like {{\"itinerary\": [{{\"action\": \"meet\", \"person\": \"David\",\"start_time\": \"13:00\", \"end_time\": \"14:00\"}}, ...]}}. Do not include location. Only keep the meeting times, and ignore time for starting, waiting, or traveling. The time should be converted to a 24-hour format. If no time range is given at all, output an empty JSON."
        
        try:
            response = client.chat.completions.create(
                model="gpt-4o-mini",  # Using gpt-4o-mini as fallback
                messages=[
                    {
                        "role": "user",
                        "content": prompt
                    }
                ],
                response_format={"type": "json_object"},
                temperature=0,
                max_tokens=2000,
                top_p=1
            )
            output_json = response.choices[0].message.content
            print(f"Extracted answer JSON: {output_json}")
            return json.loads(output_json)
        except Exception as e:
            print(f"Error in answer extraction: {e}")
            return None
    
    elif task == "trip":
        # First try to extract JSON from the response (for model outputs)
        json_pattern = r'```json\s*(\{.*?\})\s*```'
        json_match = re.search(json_pattern, text, re.DOTALL | re.IGNORECASE)
        if json_match:
            try:
                json_str = json_match.group(1)
                result = json.loads(json_str)
                if "itinerary" in result and isinstance(result["itinerary"], list):
                    return result
            except json.JSONDecodeError:
                pass
        
        # Try to find JSON without code blocks - improved pattern
        # Look for JSON objects that contain "itinerary" field
        json_pattern2 = r'\{[^}]*"itinerary"[^}]*\}'
        json_match2 = re.search(json_pattern2, text, re.DOTALL)
        if json_match2:
            try:
                # Find the complete JSON object by finding the outermost braces
                start_pos = text.rfind('{', 0, json_match2.start())
                if start_pos == -1:
                    start_pos = json_match2.start()
                
                # Find the matching closing brace
                brace_count = 0
                end_pos = start_pos
                for i in range(start_pos, len(text)):
                    if text[i] == '{':
                        brace_count += 1
                    elif text[i] == '}':
                        brace_count -= 1
                        if brace_count == 0:
                            end_pos = i + 1
                            break
                
                json_str = text[start_pos:end_pos]
                result = json.loads(json_str)
                if "itinerary" in result and isinstance(result["itinerary"], list):
                    return result
            except json.JSONDecodeError:
                pass
        
        # Try to find any JSON object that might contain itinerary
        # This is a more aggressive approach for malformed JSON
        try:
            # Look for the start of a JSON object
            start_pos = text.find('{')
            end_pos = text.rfind('}')
            if start_pos != -1 and end_pos > start_pos and 'itinerary' in text:
                json_str = text[start_pos:end_pos+1]
                result = json.loads(json_str)
                if "itinerary" in result and isinstance(result["itinerary"], list):
                    return result
        except json.JSONDecodeError:
            pass
        
        # Fallback: Parse golden trip plan format (for gold text)
        import re
        
        itinerary = []
        
        for line in text.split('\n'):
            line = line.strip()
            if not line or not line.startswith('**Day'):
                continue
                
            day_match = re.search(r'Day (\d+)(?:-(\d+))?', line)
            if not day_match:
                continue
                
            start_day = int(day_match.group(1))
            end_day = int(day_match.group(2)) if day_match.group(2) else start_day
            day_range = f"Day {start_day}-{end_day}"
            
            place_match = re.search(r'(?:Arriving in|Visit|Stay in|at) ([^\s,.]+)', line, re.IGNORECASE)
            if place_match:
                itinerary.append({
                    "day_range": day_range,
                    "place": place_match.group(1)
                })
        
        # Sort by day range start for consistent comparison
        itinerary.sort(key=lambda x: (
            int(x["day_range"].split()[1].split("-")[0]),
            x["place"]
        ))
        
        if itinerary:
            return {"itinerary": itinerary}
        
        return None
    
    return None

def format_constraint_feedback(violated_constraints, task):
    """Format constraint violations into detailed feedback for the model"""
    if not violated_constraints:
        return "All constraints are satisfied!"
    
    feedback = "The following constraints were violated:\n\n"
    
    if task == "calendar":
        if "meeting_duration" in violated_constraints:
            duration_info = violated_constraints["meeting_duration"]
            if isinstance(duration_info, dict):
                feedback += f"- Meeting duration should be {duration_info['required']} hours, but you provided {duration_info['actual']:.2f} hours\n"
            else:
                feedback += f"- Meeting duration should be {duration_info} hours\n"
        
        if "disallowed_range" in violated_constraints:
            range_info = violated_constraints["disallowed_range"]
            feedback += f"- Time conflicts with existing schedule on {range_info['day']} from {range_info['start']} to {range_info['end']}\n"
        
        if "work_hours" in violated_constraints:
            hours = violated_constraints["work_hours"]
            feedback += f"- Meeting must be within work hours (9:00-17:00)\n"
        
        if "unparsable_time_range" in violated_constraints:
            feedback += f"- Time format could not be parsed. Use format: {{HH:MM:HH:MM}}\n"
    
    elif task == "meeting":
        if "num_people_to_meet" in violated_constraints:
            num_required = violated_constraints["num_people_to_meet"]
            feedback += f"- Must meet with exactly {num_required} people\n"
        
        if "unmet_people" in violated_constraints:
            people_info = violated_constraints["unmet_people"]
            feedback += f"- Need to meet {len(people_info)} people: {', '.join(people_info)}\n"
        
        if "person_unavailable" in violated_constraints:
            person_info = violated_constraints["person_unavailable"]
            feedback += f"- {person_info['person']} is not available during the scheduled time\n"
        
        if "insufficient_travel_time" in violated_constraints:
            travel_info = violated_constraints["insufficient_travel_time"]
            feedback += f"- Insufficient travel time between {travel_info['from']} and {travel_info['to']} (need {travel_info['required']} min, have {travel_info['available']:.1f} min)\n"
        
        if "invalid_time_format" in violated_constraints:
            time_info = violated_constraints["invalid_time_format"]
            feedback += f"- Invalid time format: {time_info['start']} or {time_info['end']}\n"
    
    elif task == "trip":
        if "trip_length" in violated_constraints:
            length_info = violated_constraints["trip_length"]
            if length_info['actual'] == "invalid_start_end":
                feedback += f"- Trip must start on Day 1 and end on Day {length_info['required']}\n"
            else:
                feedback += f"- Trip must cover {length_info['required']} days, but covers {length_info['actual']}\n"
        
        if "stay_days" in violated_constraints:
            for city, required_days in violated_constraints["stay_days"].items():
                feedback += f"- Must stay in {city} for exactly {required_days} days\n"
        
        if "gap_or_overlap" in violated_constraints:
            gap_info = violated_constraints["gap_or_overlap"]
            feedback += f"- There is a gap or overlap {gap_info['between']}\n"
        
        if "flight" in violated_constraints:
            flight_info = violated_constraints["flight"]
            feedback += f"- No direct flight available from {flight_info['from']} to {flight_info['to']}\n"
        
        if "missing_place" in violated_constraints:
            feedback += f"- Missing required city: {violated_constraints['missing_place']}\n"
    
    feedback += "\nPlease revise your plan to address these issues."
    return feedback

def check_exact_match(gold_formatted, pred_formatted, task):
    """Check if prediction exactly matches gold answer"""
    if not gold_formatted or not pred_formatted:
        return False
    
    if task == "calendar":
        # Compare day and time_range
        gold_day = gold_formatted.get("day", "").lower()
        gold_time = gold_formatted.get("time_range", "")
        pred_day = pred_formatted.get("day", "").lower()
        pred_time = pred_formatted.get("time_range", "")
        
        return gold_day == pred_day and gold_time == pred_time
    
    elif task == "meeting":
        # Compare itinerary lists
        gold_itinerary = gold_formatted.get("itinerary", [])
        pred_itinerary = pred_formatted.get("itinerary", [])
        
        if len(gold_itinerary) != len(pred_itinerary):
            return False
        
        # Sort meetings for comparison
        def sort_key(meeting):
            return (meeting.get("person", ""), meeting.get("start_time", ""))
        
        gold_sorted = sorted(gold_itinerary, key=sort_key)
        pred_sorted = sorted(pred_itinerary, key=sort_key)
        
        for gold_meeting, pred_meeting in zip(gold_sorted, pred_sorted):
            if (gold_meeting.get("person", "").lower() != pred_meeting.get("person", "").lower() or
                gold_meeting.get("start_time", "") != pred_meeting.get("start_time", "") or
                gold_meeting.get("end_time", "") != pred_meeting.get("end_time", "")):
                return False
        
        return True
    
    elif task == "trip":
        # Compare itinerary
        gold_itinerary = gold_formatted.get("itinerary", [])
        pred_itinerary = pred_formatted.get("itinerary", [])
        
        if len(gold_itinerary) != len(pred_itinerary):
            return False
        
        for gold_item, pred_item in zip(gold_itinerary, pred_itinerary):
            if (gold_item.get("day_range") != pred_item.get("day_range") or
                gold_item.get("place", "").lower() != pred_item.get("place", "").lower()):
                return False
        
        return True
    
    return False

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
    """Process a single example with iterative refinement"""
    # Initialize variables that might be referenced in error handling
    gold_text = ""
    gold_formatted = {}
    pred_formatted = {}
    violated_constraints = {}
    is_exact_match = False
    constraints_satisfied = False
    response_text = ""
    pass_num = 0
    
    try:
        logging.info(f"[{example_id}] Starting processing with model {model}")
        
        # Create output directory
        output_dir = f"../output/Plan/{model}/{task}/n_pass/{example_id}"
        os.makedirs(output_dir, exist_ok=True)
        
        # Initialize AI model (outside semaphore to allow parallel initialization)
        try:
            logging.info(f"[{example_id}] About to initialize model...")
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
        
        # Get gold answer text (for reference only, not for exact match)
        gold_text = extract_gold_answer(example, task)
        logging.info(f"[{example_id}] Pass {pass_num} gold text: {gold_text[:100] if gold_text else 'None'}...")
        
        # Initial prompt
        if task == "calendar":
            prompt = example.get("prompt_0shot", "")
            prompt += "\n\nIMPORTANT: Do NOT write any code or algorithms. Simply provide the answer in the following JSON format:\n{\"time_range\": \"{HH:MM:HH:MM}\", \"day\": \"<DAY>\"}\n\nFor example, if the proposed time is Tuesday, 14:30 to 15:30, the output should be:\n{\"time_range\": \"{14:30:15:30}\", \"day\": \"Tuesday\"}"
        elif task == "meeting":
            prompt = example.get("prompt_0shot", "")
            prompt += "\n\nPlease output the meeting schedule in the following JSON format:\n{\"itinerary\": [{\"action\": \"meet\", \"person\": \"<PERSON_NAME>\", \"start_time\": \"<HH:MM>\", \"end_time\": \"<HH:MM>\"}]}. Make sure to include the person's name for each meeting."
        elif task == "trip":
            prompt = example.get("prompt_0shot", "")
            prompt += "\n\nPlease output the trip plan in the following JSON format:\n{\"itinerary\": [{\"day_range\": \"Day X-Y\", \"place\": \"<CITY>\"}]}. Include all city visits with their day ranges. Do not include separate flight entries in the JSON output.\n\nIMPORTANT: When you fly from city A to city B on day X, that day counts for BOTH cities. For example:\n- If you stay in Venice from Day 1-3 and fly to Vienna on Day 3, then:\n  - Venice: Day 1-3 (3 days)\n  - Vienna: Day 3-6 (4 days, including the flight day)\n- The flight day (Day 3) is counted for both Venice and Vienna.\n- Do NOT create separate flight entries in the JSON."
        
        current_prompt = prompt
        
        for pass_num in range(1, max_passes + 1):
            pass_start_time = time.time()
            logging.info(f"[{example_id}] Starting pass {pass_num}")
            
            # Create output directory for this pass
            pass_output_dir = f"{output_dir}/{pass_num}_pass"
            os.makedirs(pass_output_dir, exist_ok=True)
            
            # Get response from model with rate limiting (use semaphore only for API calls)
            api_call_start = time.time()
            retry_count = 0
            max_retries = 3
            while retry_count < max_retries:
                try:
                    logging.info(f"[{example_id}] Making API call (attempt {retry_count + 1})")
                    # Use semaphore only for the actual API call
                    async with semaphore:
                        response_text = await run_model_with_rate_limit(ai, current_prompt, rate_limiter)
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
            
            # Add to conversation history
            conversation_history.append({"role": "user", "content": current_prompt})
            conversation_history.append({"role": "assistant", "content": response_text})
            
            # Save conversation
            with open(f"{pass_output_dir}/conversation.json", "w") as f:
                json.dump(conversation_history, f, indent=4)
            
            # Extract prediction
            try:
                pred_formatted = extract_answer_from_text(response_text, task)
                logging.info(f"[{example_id}] Pass {pass_num} extracted prediction: {pred_formatted}")
            except Exception as e:
                logging.error(f"[{example_id}] Pass {pass_num} failed to extract prediction: {str(e)}")
                pred_formatted = {}
            
            # Save plan
            with open(f"{pass_output_dir}/plan.json", "w") as f:
                json.dump(pred_formatted, f, indent=4)
            
            # Set num_people_to_meet from constraints for meeting tasks
            if task == "meeting":
                # Use num_people_to_meet from constraints if available, otherwise use people_to_meet length
                if "num_people_to_meet" not in constraints:
                    people_to_meet = constraints.get("people_to_meet", [])
                    constraints["num_people_to_meet"] = len(people_to_meet)
            
            # Evaluate constraints
            if task == "calendar":
                constraints_satisfied, violated_constraints = evaluate_calendar(constraints, pred_formatted)
            elif task == "meeting":
                constraints_satisfied, violated_constraints = evaluate_meeting(constraints, pred_formatted)
            elif task == "trip":
                constraints_satisfied, violated_constraints = evaluate_trip(constraints, pred_formatted)
            
            logging.info(f"[{example_id}] Pass {pass_num} constraints satisfied: {constraints_satisfied}")
            logging.info(f"[{example_id}] Pass {pass_num} violated constraints: {violated_constraints}")
            
            # Extract structured gold data for exact match comparison and evaluation
            if gold_text:
                gold_formatted = extract_answer_from_text(gold_text, task)
            
            # Check exact match
            if gold_formatted and pred_formatted:
                is_exact_match = check_exact_match(gold_formatted, pred_formatted, task)
            else:
                is_exact_match = False
            logging.info(f"[{example_id}] Pass {pass_num} exact match: {is_exact_match}")
            
            # Determine status - check exact match first, then constraints
            if is_exact_match:
                status = "Exact match"
                constraints_satisfied = True  # Exact match implies constraints are satisfied
            elif constraints_satisfied:
                status = "Correct plan (constraints satisfied)"
            else:
                status = "Wrong plan"
            
            # Save evaluation
            eval_result = {
                "has_execution_error": False,
                "execution_output": response_text,
                "pred": pred_formatted,
                "gold": gold_formatted if gold_text and pred_formatted else {},
                "status": status,
                "violated_constraint": violated_constraints,
                "is_exact_match": is_exact_match,
                "constraints_satisfied": constraints_satisfied,
                "pass_number": pass_num
            }
            with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                json.dump(eval_result, f, indent=4)
            
            if is_exact_match or constraints_satisfied:
                if is_exact_match:
                    logging.info(f"[{example_id}] SUCCESS! Exact match in pass {pass_num}")
                else:
                    logging.info(f"[{example_id}] SUCCESS! Constraints satisfied in pass {pass_num}")
                return
            else:
                logging.info(f"[{example_id}] Pass {pass_num} failed both exact match and constraints, preparing feedback")
                # Prepare feedback for next iteration
                constraint_feedback = format_constraint_feedback(violated_constraints, task)
                current_prompt = f"The previous solution produced the following output:\n{response_text}\n{constraint_feedback}\n\nPlease revise your solution to satisfy these constraints."
        
        logging.warning(f"[{example_id}] FAILED to solve within {max_passes} passes")
        
        # Save final evaluation result even if we failed to solve
        if 'pred_formatted' in locals():
            final_eval_result = {
                "has_execution_error": False,
                "execution_output": response_text,
                "pred": pred_formatted,
                "gold": gold_formatted if 'gold_formatted' in locals() else {},
                "status": "Failed to solve within max passes",
                "violated_constraint": violated_constraints,
                "is_exact_match": is_exact_match,
                "constraints_satisfied": constraints_satisfied,
                "pass_number": pass_num
            }
            with open(f"{pass_output_dir}/evaluation.json", "w") as f:
                json.dump(final_eval_result, f, indent=4)
            logging.info(f"[{example_id}] Saved final evaluation result from pass {pass_num}")
        
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
    """Main function"""
    args = parse_args()
    
    # Load examples and constraints
    examples = load_examples(args.task)
    constraints = load_constraints(args.task)
    
    # Filter examples based on arguments
    if args.examples:
        example_numbers = [int(x) for x in args.examples.split(',')]
        examples = {k: v for k, v in examples.items() if any(str(num) in k for num in example_numbers)}
    elif args.start is not None or args.end is not None:
        start = args.start or 0
        end = args.end or len(examples)
        example_items = list(examples.items())[start:end]
        examples = dict(example_items)
    
    logging.info(f"Starting processing of {len(examples)} examples")
    
    # Initialize rate limiter and semaphore
    rate_limiter = RateLimiter(args.rate_limit)
    semaphore = asyncio.Semaphore(args.max_concurrent)
    
    # Process examples in parallel
    tasks = []
    for example_id, example in examples.items():
        logging.info(f"Creating task for {example_id}")
        task = asyncio.create_task(
            process_single_example(
                example_id,
                example,
                constraints.get(example_id, {}),
                args.model,
                args.max_passes,
                rate_limiter,
                semaphore,
                args.task,
                args
            )
        )
        tasks.append(task)
        logging.info(f"Task created for {example_id}")
    
    logging.info(f"All {len(tasks)} tasks created, waiting for completion...")
    
    # Wait for all tasks to complete
    results = await asyncio.gather(*tasks, return_exceptions=True)
    
    # Log results
    success_count = sum(1 for r in results if not isinstance(r, Exception))
    error_count = len(results) - success_count
    logging.info(f"Completed processing {len(results)} examples: {success_count} successful, {error_count} failed")

def load_examples(task):
    """Load examples for the specified task"""
    if task == "calendar":
        with open("../data/calendar_scheduling_100.json", 'r') as f:
            return json.load(f)
    elif task == "meeting":
        with open("../data/meeting_planning_100.json", 'r') as f:
            return json.load(f)
    elif task == "trip":
        with open("../data/trip_planning_100.json", 'r') as f:
            return json.load(f)
    else:
        raise ValueError(f"Unknown task: {task}")

def load_constraints(task):
    """Load constraints from the appropriate JSON file - consistent with SMT program"""
    task_name_map = {
        "calendar": "calendar_scheduling",
        "trip": "trip_planning",
        "meeting": "meeting_planning"
    }
    with open(f"../data/{task_name_map[task]}_100_constraints.json") as f:
        constraints_data = json.load(f)
        return {example_id: data.get("constraints", {}) for example_id, data in constraints_data.items()}

def extract_gold_answer(example, task):
    """Extract gold answer from example - simplified to just return the golden_plan text"""
    # For evaluation purposes, we only need the golden_plan text
    # We don't need to parse it into structured format since we only evaluate constraints
    return example.get("golden_plan", "")

if __name__ == "__main__":
    asyncio.run(main()) 