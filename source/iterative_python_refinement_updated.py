"""
Parallel Scheduling Program with Iterative LLM Refinement

This program solves calendar scheduling, meeting planning, and trip planning problems using LLMs
to generate and iteratively refine Python solutions. It processes multiple examples in parallel
with rate limiting and provides detailed feedback on constraint violations and execution errors.
"""

import argparse
import asyncio
import json
import logging
import os
import re
import subprocess
import sys
import time
from datetime import datetime
import time
from typing import Dict, List, Tuple, Optional, Union
import tiktoken
from openai import OpenAI
from kani.engines.openai import OpenAIEngine
from kani import Kani
from kani.engines.huggingface import HuggingEngine

current_time = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler(f'scheduling_program_{current_time}.log')
    ]
)

class RateLimiter:
    def __init__(self, requests_per_second: float):
        self.requests_per_second = requests_per_second
        self.last_request_time = 0
        self.lock = asyncio.Lock()
    
    async def wait(self):
        async with self.lock:  # Add this lock to prevent concurrent access
            if self.requests_per_second <= 0:
                return
            
            current_time = time.time()
            time_since_last = current_time - self.last_request_time
            min_interval = 1.0 / self.requests_per_second
            
            if time_since_last < min_interval:
                wait_time = min_interval - time_since_last
                await asyncio.sleep(wait_time)
            
            self.last_request_time = time.time()

class SchedulingProgram:
    def __init__(self):
        self.args = self.parse_arguments()
        self.setup_directories()
        
        # Determine task name for file naming
        self.task_name = self.args.task if self.args.task != "all" else "all_tasks"
        
        # Configure logging with task-specific filename
        self.configure_logging()
        
        self.initialize_models()
        self.state = EvaluationState(self.task_name)  # Pass task name to EvaluationState
        self.state.load()
        
        # Load all prompts and constraints
        self.load_data()
        
        # Initialize rate limiter
        self.rate_limiter = RateLimiter(self.args.rate_limit)
        
        # Task-specific configurations
        self.task_config = {
            "calendar": {
                "prefix": self.calendar_prefix,
                "suffix": self.calendar_suffix,
                "parse_golden": self.parse_calendar_golden,
                "parse_output": self.parse_calendar_output,
                "evaluate": self.evaluate_calendar,
                "format_feedback": self.format_calendar_feedback
            },
            "meeting": {
                "prefix": self.meeting_prefix,
                "suffix": self.meeting_suffix,
                "parse_golden": self.parse_meeting_golden,
                "parse_output": self.parse_meeting_output,
                "evaluate": self.evaluate_meeting,
                "format_feedback": self.format_meeting_feedback
            },
            "trip": {
                "prefix": self.trip_prefix,
                "suffix": self.trip_suffix,
                "parse_golden": self.parse_trip_golden,
                "parse_output": self.parse_trip_output,
                "evaluate": self.evaluate_trip,
                "format_feedback": self.format_trip_feedback
            }
        }

    def configure_logging(self):
        """Configure logging with task-specific filename"""
        log_filename = f'scheduling_{self.task_name}_{current_time}.log'
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s',
            handlers=[
                logging.StreamHandler(sys.stdout),
                logging.FileHandler(log_filename)
            ]
        )

    def parse_arguments(self):
        parser = argparse.ArgumentParser(
            description="Combined Scheduling Program",
            formatter_class=argparse.RawDescriptionHelpFormatter,
            epilog="""
Examples:
  # Run calendar scheduling with DeepSeek-V3 on examples 0-4
  python scheduling_program.py --task calendar --model DeepSeek-V3 --start 0 --end 5
  
  # Run all tasks with multiple models, max 3 passes per example
  python scheduling_program.py --task all --model DeepSeek-V3 gpt-4o-mini --max_passes 3
  
  # Force re-run all examples (ignore existing results)
  python scheduling_program.py --task meeting --model DeepSeek-R1 --fresh
  
  # Run with parallel processing (10 concurrent examples)
  python scheduling_program.py --task trip --model DeepSeek-V3 --max_concurrent 10 --rate_limit 5
"""
        )
        parser.add_argument('--task', choices=['calendar', 'trip', 'meeting', 'all'], required=True,
                          help="Task to run: calendar, trip, meeting, or all")
        parser.add_argument('--model', required=True, nargs='+',
                          help="Model(s) to use: DeepSeek-V3, DeepSeek-R1, or any HuggingFace model path")
        parser.add_argument('--fresh', action='store_true',
                          help="Re-run all examples, ignoring existing successful solutions")
        parser.add_argument('--start', type=int, default=0,
                          help="Starting index for processing examples (default: 0)")
        parser.add_argument('--end', type=int, default=-1,
                          help="Ending index for processing examples (default: -1, process all)")
        parser.add_argument('--max_passes', type=int, default=5,
                          help="Maximum number of refinement passes per example (default: 5)")
        parser.add_argument('--max_concurrent', type=int, default=5,
                          help="Maximum number of examples to process concurrently")
        parser.add_argument('--rate_limit', type=float, default=1.0,
                          help="Requests per second limit (to avoid API rate limits)")
        parser.add_argument('--api_key_file', type=str, default='../../openai_research/deepseek_api_key.json',
                          help="Path to file containing API keys")
        parser.add_argument('--examples', type=str,
                          help="Comma-separated list of specific example numbers to run")
        return parser.parse_args()

    def setup_directories(self):
        """Ensure all required directories exist"""
        os.makedirs("output", exist_ok=True)
        for task in ["calendar", "meeting", "trip"]:
            os.makedirs(f"output/{task}", exist_ok=True)

    def initialize_models(self):
        """Initialize all requested models using proper kani pattern"""
        try:
            with open(self.args.api_key_file) as f:
                self.keys = json.load(f)
        except FileNotFoundError:
            logging.error(f"API key file {self.args.api_key_file} not found")
            sys.exit(1)
        except json.JSONDecodeError:
            logging.error(f"Invalid JSON in API key file {self.args.api_key_file}")
            sys.exit(1)

        self.engines = {}  # Store all engines here
        
        for model_name in self.args.model:
            try:
                if model_name.startswith("DeepSeek"):
                    # Treat DeepSeek like any other OpenAI model
                    self.engines[model_name] = OpenAIEngine(
                        api_key=self.keys.get("deepseek"),
                        model="deepseek-chat" if model_name == "DeepSeek-V3" else "deepseek-reasoner",
                        api_base="https://api.deepseek.com",
                        max_context_size=50000
                    )
                elif model_name.startswith("gpt"):
                    self.engines[model_name] = OpenAIEngine(
                        api_key=self.keys.get("openai"), 
                        model=model_name
                    )
                else:
                    # HuggingFace model
                    self.engines[model_name] = HuggingEngine(model_id=model_name)
                    
            except Exception as e:
                logging.error(f"Failed to initialize model {model_name}: {e}")

    async def get_model_instance(self, model_name):
        """Get a fresh Kani instance for each request"""
        if model_name not in self.engines:
            raise ValueError(f"Model {model_name} not initialized")
        
        # Create new Kani instance with the engine
        return Kani(self.engines[model_name], system_prompt="")

    def load_data(self):
        """Load all prompts and constraints"""
        self.prompts = {}
        self.constraints = {}
        
        # Calendar data
        try:
            with open("../data/calendar_scheduling_100.json") as f:
                self.prompts["calendar"] = json.load(f)
            with open("../data/calendar_scheduling_100_constraints.json") as f:
                self.constraints["calendar"] = json.load(f)
        except FileNotFoundError as e:
            logging.warning(f"Calendar data files not found: {e}")
        
        # Meeting data
        try:
            with open("../data/meeting_planning_100.json") as f:
                self.prompts["meeting"] = json.load(f)
            with open("../data/meeting_planning_100_constraints.json") as f:
                self.constraints["meeting"] = json.load(f)
        except FileNotFoundError as e:
            logging.warning(f"Meeting data files not found: {e}")
        
        # Trip data
        try:
            with open("../data/trip_planning_100.json") as f:
                self.prompts["trip"] = json.load(f)
            with open("../data/trip_planning_100_constraints.json") as f:
                self.constraints["trip"] = json.load(f)
        except FileNotFoundError as e:
            logging.warning(f"Trip data files not found: {e}")

    # Task-specific prompt components
    @property
    def calendar_prefix(self):
        return (
            "You are an expert at scheduling meetings. Your task is to find a suitable time for a meeting "
            "based on the participants' schedules and constraints. In this case:\n"
        )

    @property
    def calendar_suffix(self):
        return (
            "\nGenerate a fully working Python script with code that calculates a proposed time and outputs it in the format HH:MM:HH:MM. "
            "The script should also output the day of the week (e.g., Monday, Tuesday). "
            "The script should be clean, well-formatted, and enclosed within ```python and ```. "
            "The output of the generated code must include both the time range (like {14:30:15:30}) and the day of the week. "
            "Provide the response with only code."
        )

    @property
    def meeting_prefix(self):
        return (
            "You are an expert computational meeting planner. Your task is to write a Python program that "
            "algorithmically calculates the optimal meeting schedule based on the participants' constraints.\n"
            "The program must actually compute the plan using the given parameters, not just print a pre-determined answer.\n"
            "Input parameters:\n"
        )

    @property
    def meeting_suffix(self):
        return (
            "\n\nGenerate a complete, self-contained Python program that:\n"
            "1. Takes the above meeting constraints as input variables\n"
            "2. Computes the optimal meeting schedule using logical rules and calculations\n"
            "3. Outputs the result as a JSON-formatted dictionary with the following structure:\n"
            "{\n"
            '  "itinerary": [\n'
            '    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"},\n'
            '    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"}\n'
            "  ]\n"
            "}\n"
            "Rules for the program:\n"
            "- Times should be in 24-hour format like '9:00' or '13:30' (no leading zero)\n"
            "- The schedule must account for all travel times and constraints\n"
            "- The program must actually compute the schedule, not just print a static answer\n"
            "\n"
            "Output only the complete Python code with no additional text or explanation.\n"
            "The code must run independently and output valid JSON when executed."
        )

    @property
    def trip_prefix(self):
        return (
            "You are an expert computational trip planner.\n"
            "Your task is to write a Python program that algorithmically calculates the optimal itinerary based on the participants' constraints.\n"
            "The program must actually compute the plan using the given parameters, not just print a predetermined answer.\n"
        )

    @property
    def trip_suffix(self):
        return (
            "\n\nGenerate a complete, self-contained Python program that:\n"
            "1. Takes the above trip constraints as input variables\n"
            "2. Computes the optimal itinerary using logical rules and calculations\n"
            "3. Outputs the result as a JSON-formatted dictionary with an 'itinerary' key containing a list of day-place mappings.\n"
            "Example structure of output from running code: {\"itinerary\": [{\"day_range\": \"Day 1-5\", \"place\": \"Helsinki\"}, {\"day_range\": \"Day 5-9\", \"place\": \"Barcelona\"}, {\"day_range\": \"Day 9-14\", \"place\": \"Florence\"}]}\n"
            "Note that the JSON structure should be what the Python program outputs, not just a string representation.\n"
            "4. Note that if one flies from city A to city B on day X, then they are in both cities A and B on day X, which contributes to the total number of days in each city.\n"
            "The program must include:\n"
            "- Actual calculations to determine durations and transitions\n"
            "Output only the complete Python code with no additional text or explanation.\n"
            "The code must run independently and output valid JSON when executed."
        )
    
    def remove_leading_zeros(self, time_str):
        """Remove leading zeros from time strings (e.g., '09:00' -> '9:00')"""
        if not time_str:
            return time_str
        
        # Split into hours and minutes
        parts = time_str.split(':')
        if len(parts) >= 1:
            # Remove leading zero from hour part
            parts[0] = str(int(parts[0]))
        
        return ':'.join(parts)

    # Task-specific parsing and evaluation methods
    def parse_calendar_golden(self, golden_plan):
        """Parse the golden plan into a structured format with consistent ordering."""
        match = re.search(r'(\w+), (\d{1,2}:\d{2}) - (\d{1,2}:\d{2})', golden_plan)
        if match:
            day_of_week, start_time, end_time = match.groups()
            time_range = f"{{{start_time}:{end_time}}}"
            return {
                "day": day_of_week,
                "time_range": time_range
            }
        return {
            "day": "Invalid day format", 
            "time_range": "Invalid time format"
        }

    def parse_calendar_output(self, output):
        """Parse model output into same structured format as golden, with consistent ordering."""
        if not output:
            return None
        
        # First try to extract structured answer using GPT-4.1-nano
        try:
            extracted = self.extract_answer(output, "calendar")
            if extracted and "day" in extracted and "start_time" in extracted and "end_time" in extracted:
                # Remove leading zeros from times
                start_time = self.remove_leading_zeros(extracted['start_time'])
                end_time = self.remove_leading_zeros(extracted['end_time'])
                time_output = f"{{{start_time}:{end_time}}}"
                return {
                    "day": extracted["day"],
                    "time_range": time_output
                }
        except Exception as e:
            logging.warning(f"Error extracting answer with GPT-4.1-nano: {e}")

        # Fall back to original parsing if extraction fails
        day_match = re.search(r'(Monday|Tuesday|Wednesday|Thursday|Friday|Saturday|Sunday)', 
                            output, re.IGNORECASE)
        day = day_match.group(0) if day_match else None
        
        time_pattern = re.compile(r"\b\d{2}:\d{2}:\d{2}:\d{2}\b")
        time_match = time_pattern.search(output)
        if time_match:
            time_str = time_match.group(0)
            parts = time_str.strip("{}").split(":")
            # Remove leading zeros from hour parts
            parts[0] = str(int(parts[0]))
            parts[2] = str(int(parts[2]))
            time_output = f"{{{':'.join(parts)}}}"
            return {
                "day": day,
                "time_range": time_output
            }
        return None

    def evaluate_calendar(self, constraints, predicted_output):
        """Evaluate calendar constraints using structured output format."""
        if not predicted_output or "day" not in predicted_output or "time_range" not in predicted_output:
            return False, {"missing_fields": True}

        predicted_day = predicted_output["day"]
        predicted_time = predicted_output["time_range"]
        
        # Convert time strings to numerical values
        try:
            start_parts = predicted_time.strip("{}").split(":")[0:2]
            end_parts = predicted_time.strip("{}").split(":")[2:4]
            pred_start = float(start_parts[0]) + float(start_parts[1]) / 60
            pred_end = float(end_parts[0]) + float(end_parts[1]) / 60
        except (ValueError, IndexError):
            return False, {"unparsable": True}

        meeting_duration = constraints.get("meeting_duration", 0)
        if (pred_end - pred_start) != meeting_duration:
            return False, {"meeting_duration": meeting_duration}

        for disallowed_range in constraints.get("disallowed_ranges", []):
            if disallowed_range["day"] == predicted_day:
                if (pred_start >= disallowed_range["start"] and pred_start < disallowed_range["end"]) or \
                        (pred_end > disallowed_range["start"] and pred_end <= disallowed_range["end"]) or \
                        (pred_start <= disallowed_range["start"] and pred_end >= disallowed_range["end"]):
                    return False, disallowed_range
        return True, {}

    def format_calendar_feedback(self, violated_constraints):
        if not violated_constraints:
            return ""
        
        feedback = "\nYour solution violates the following constraints:\n"
        if "meeting_duration" in violated_constraints:
            feedback += f"- The meeting duration must be exactly {violated_constraints['meeting_duration']} hours\n"
        if "day" in violated_constraints and "start" in violated_constraints:
            feedback += f"- The meeting time conflicts with an unavailable time slot on {violated_constraints['day']} from {violated_constraints['start']} to {violated_constraints['end']}\n"
        feedback += "\nPlease revise your solution to satisfy these constraints."
        return feedback

    def parse_meeting_golden(self, golden_plan):
        """Parse the golden plan into a structured format with 'itinerary' key."""
        itinerary = []
        current_location = None
        
        for step in golden_plan:
            step = step.strip()
            if not step:
                continue
                
            # Parse start action
            if step.startswith("You start at"):
                match = re.search(r"You start at (.+?) at (.+?)\.", step)
                if match:
                    current_location = match.group(1)
                    
            # Parse travel action
            elif "travel to" in step:
                match = re.search(r"You travel to (.+?) in (\d+) minutes and arrive at (.+?)\.", step)
                if match:
                    current_location = match.group(1)
                    
            # Parse meet action
            elif "meet" in step and "for" in step:
                match = re.search(r"You meet (.+?) for (\d+) minutes from (.+?) to (.+?)\.", step)
                if match and current_location:
                    person = match.group(1)
                    start_time = self.convert_to_24hr_no_leading_zero(match.group(3))
                    end_time = self.convert_to_24hr_no_leading_zero(match.group(4))
                    
                    itinerary.append({
                        "action": "meet",
                        "location": current_location,
                        "person": person,
                        "start_time": start_time,
                        "end_time": end_time
                    })
                    
        # Return with 'itinerary' key to match predicted output structure
        return {"itinerary": itinerary}

    def parse_meeting_output(self, output):
        """Parse meeting output with consistent itinerary ordering."""
        if not output:
            return None
        
        # First try to extract structured answer using GPT-4.1-nano
        try:
            extracted = self.extract_answer(output, "meeting")
            if extracted and "itinerary" in extracted:
                normalized = self.normalize_meeting_itinerary(extracted)
                if normalized and "itinerary" in normalized:
                    # Sort by start time for consistent comparison
                    normalized["itinerary"].sort(key=lambda x: (
                        datetime.strptime(x.get("start_time", "00:00"), "%H:%M"),
                        x.get("person", "")
                    ))
                return normalized
        except Exception as e:
            logging.warning(f"Error extracting answer with GPT-4.1-nano: {e}")

        # Fall back to original parsing if extraction fails
        if isinstance(output, dict):
            normalized = self.normalize_meeting_itinerary(output)
            if normalized and "itinerary" in normalized:
                normalized["itinerary"].sort(key=lambda x: (
                    datetime.strptime(x.get("start_time", "00:00"), "%H:%M"),
                    x.get("person", "")
                ))
            return normalized
        
        if isinstance(output, str):
            output = output.strip()
            if output.startswith("SOLUTION:"):
                output = output[len("SOLUTION:"):].strip()
        
        try:
            if isinstance(output, str):
                itinerary_data = json.loads(output)
                normalized = self.normalize_meeting_itinerary(itinerary_data)
                if normalized and "itinerary" in normalized:
                    normalized["itinerary"].sort(key=lambda x: (
                        datetime.strptime(x.get("start_time", "00:00"), "%H:%M"),
                        x.get("person", "")
                    ))
                return normalized
        except json.JSONDecodeError:
            pass
        
        json_pattern = r'\{.*?"itinerary"\s*:\s*\[.*?\]\}'
        matches = re.search(json_pattern, output, re.DOTALL)
        if matches:
            try:
                itinerary_data = json.loads(matches.group(0))
                normalized = self.normalize_meeting_itinerary(itinerary_data)
                if normalized and "itinerary" in normalized:
                    normalized["itinerary"].sort(key=lambda x: (
                        datetime.strptime(x.get("start_time", "00:00"), "%H:%M"),
                        x.get("person", "")
                    ))
                return normalized
            except json.JSONDecodeError:
                pass
        
        dict_pattern = r'\{[\s\S]*?\}'
        matches = re.findall(dict_pattern, output)
        if matches:
            for match in reversed(matches):
                try:
                    itinerary_data = json.loads(match)
                    if "itinerary" in itinerary_data:
                        normalized = self.normalize_meeting_itinerary(itinerary_data)
                        if normalized and "itinerary" in normalized:
                            normalized["itinerary"].sort(key=lambda x: (
                                datetime.strptime(x.get("start_time", "00:00"), "%H:%M"),
                                x.get("person", "")
                            ))
                        return normalized
                except json.JSONDecodeError:
                    continue
        
        return None

    def normalize_meeting_itinerary(self, itinerary_data):
        """Normalize meeting itinerary with consistent field ordering."""
        if not isinstance(itinerary_data, dict) or "itinerary" not in itinerary_data:
            return None
        
        itinerary = itinerary_data.get("itinerary", [])
        normalized_itinerary = []
        
        for step in itinerary:
            if not isinstance(step, dict):
                continue
                
            action = step.get("action", "").lower()
            if action != "meet":
                continue
                
            normalized_step = {
                "action": action,
                "location": step.get("location", "Unknown"),  # Keep original location or default to "Unknown"
                "person": step.get("person", "Unknown"),
                "start_time": self.convert_to_24hr_no_leading_zero(step.get("start_time", "")),
                "end_time": self.convert_to_24hr_no_leading_zero(step.get("end_time", ""))
            }
            
            normalized_itinerary.append(normalized_step)
        
        return {"itinerary": normalized_itinerary}

    def evaluate_meeting(self, constraints, predicted_itinerary):
        """Evaluate meeting plan against constraints with structured comparison."""
        if not predicted_itinerary or "itinerary" not in predicted_itinerary:
            return False, {"missing_itinerary": True}

        # Ensure golden output has same structure
        golden_itinerary = {"itinerary": self.parse_meeting_golden(constraints.get("golden_plan", []))["itinerary"]}
        
        # First check for exact match of structured plans
        if predicted_itinerary == golden_itinerary:
            return True, {}
        
        people = {p["name"]: p for p in constraints.get("people_to_meet", [])}
        start_location = constraints.get("start", {}).get("location")
        start_time_str = constraints.get("start", {}).get("time_of_day")
        num_people_to_meet = constraints.get("num_people_to_meet", 0)

        meetings = []
        if isinstance(predicted_itinerary["itinerary"], list):
            for m in predicted_itinerary["itinerary"]:
                if isinstance(m, dict):
                    name = m.get("person")
                    start = self.parse_time(m.get("start_time"))
                    end = self.parse_time(m.get("end_time"))
                    if start is None or end is None:
                        return False, {"invalid_time_format": {"start": m.get("start_time"), "end": m.get("end_time")}}
                    loc = people.get(name, {}).get("location")
                    meetings.append({"person": name, "start": start, "end": end, "location": loc})

        if len(meetings) < num_people_to_meet:
            return False, {"num_people_to_meet": num_people_to_meet}

        if not meetings:
            return False, {"no_valid_meetings": True}

        meetings.sort(key=lambda x: x["start"])

        for m in meetings:
            p = people.get(m["person"])
            if not p:
                continue
            avail = p["time_of_day"]
            av_from = self.parse_time(avail["from"])
            av_to = self.parse_time(avail["to"])
            if m["start"] < av_from or m["end"] > av_to:
                return False, {"person": m["person"], "time_of_day": avail}

        travel = {}
        for d in constraints.get("travel_distances", []):
            pl = d["place"]
            frm = pl.get("from", constraints.get("start", {}).get("location"))
            to = pl["to"]
            travel[(frm, to)] = d["walking_time"]

        if start_time_str:
            st = self.parse_time(start_time_str)
            first = meetings[0]
            
            # Convert times to datetime for calculation
            today = datetime.today()
            first_start = datetime.combine(today, first["start"])
            st_time = datetime.combine(today, st)
            
            gap0 = (first_start - st_time).total_seconds() / 60
            walk0 = travel.get((start_location, first["location"]))
            if walk0 is not None and walk0 > gap0:
                return False, {
                    "travel_start": {
                        "to_person": first["person"],
                        "to_location": first["location"],
                        "travel_time": walk0
                    }
                }

        for a, b in zip(meetings, meetings[1:]):
            # Convert times to datetime for calculation
            today = datetime.today()
            a_end = datetime.combine(today, a["end"])
            b_start = datetime.combine(today, b["start"])
            
            gap_mins = (b_start - a_end).total_seconds() / 60
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

        return False, {"constraints_satisfied_but_no_exact_match": True}

    def format_meeting_feedback(self, violated_constraints):
        if not violated_constraints:
            return ""
        
        feedback = "\nYour solution violates the following constraints:\n"
        if "num_people_to_meet" in violated_constraints:
            feedback += f"- Must meet with exactly {violated_constraints['num_people_to_meet']} people\n"
        if "travel" in violated_constraints:
            travel = violated_constraints["travel"]
            feedback += f"- Not enough time to travel from {travel['from_location']} to {travel['to_location']} (need {travel['travel_time']} minutes)\n"
        if "person" in violated_constraints:
            feedback += f"- Meeting time with {violated_constraints['person']} is outside their availability\n"
        feedback += "\nPlease revise your solution to satisfy these constraints."
        return feedback

    def parse_trip_golden(self, golden_plan):
        """Parse golden trip plan with consistent ordering."""
        itinerary = []
        
        for line in golden_plan.split('\n'):
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
        return {"itinerary": itinerary}

    def parse_trip_output(self, output):
        """Parse trip output with consistent itinerary ordering."""
        if not output:
            return None
        
        # First try to extract structured answer using GPT-4.1-nano
        try:
            extracted = self.extract_answer(output, "trip")
            if extracted and "itinerary" in extracted:
                # Sort by day range start for consistent comparison
                extracted["itinerary"].sort(key=lambda x: (
                    int(x["day_range"].split()[1].split("-")[0]),
                    x["place"]
                ))
                return extracted
        except Exception as e:
            logging.warning(f"Error extracting answer with GPT-4.1-nano: {e}")

        try:
            if isinstance(output, str):
                parsed = json.loads(output)
            else:
                parsed = output
            
            normalized_itinerary = []
            
            if "itinerary" in parsed:
                items = parsed["itinerary"]
            elif isinstance(parsed, list):
                items = parsed
            else:
                return None
            
            for item in items:
                if isinstance(item, dict):
                    normalized_item = {}
                    
                    if "day_range" in item:
                        normalized_item["day_range"] = item["day_range"]
                    elif "days" in item:
                        days = item["days"].split("-")
                        normalized_item["day_range"] = f"Day {days[0]}-{days[1]}"
                    
                    if "place" in item:
                        normalized_item["place"] = item["place"]
                    elif "location" in item:
                        normalized_item["place"] = item["location"]
                    
                    if "day_range" in normalized_item and "place" in normalized_item:
                        normalized_itinerary.append(normalized_item)
            
            if normalized_itinerary:
                # Sort by day range start for consistent comparison
                normalized_itinerary.sort(key=lambda x: (
                    int(x["day_range"].split()[1].split("-")[0]),
                    x["place"]
                ))
                return {"itinerary": normalized_itinerary}
            
        except json.JSONDecodeError:
            return None
        except Exception as e:
            logging.error(f"Error parsing trip output: {e}")
            return None

    def evaluate_trip(self, constraints, predicted_itinerary):
        if not predicted_itinerary or "itinerary" not in predicted_itinerary:
            return False, {"missing_itinerary": True}
            
        segments = []
        for seg in predicted_itinerary["itinerary"]:
            if not seg["day_range"].startswith("Day ") or "{" in seg["day_range"] or "}" in seg["day_range"]:
                return False, {"invalid_day_range_format": seg["day_range"]}

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

        total = constraints.get("trip_length")
        if not segments or segments[0]["start"] != 1 or segments[-1]["end"] != total:
            return False, {"total_days": total}

        for a, b in zip(segments, segments[1:]):
            if a["end"] != b["start"]:
                return False, {"gap/overlap": (a, b)}

        for seg in segments:
            required = constraints.get("stay_days", {}).get(seg["place"])
            if required is not None:
                actual = seg["end"] - seg["start"] + 1
                if actual != required:
                    return False, {"stay_days": {seg["place"]: required}}

        for ev in constraints.get("city_day_ranges", []):
            place = ev["city"]
            container = next((s for s in segments if s["place"] == place), None)
            if not container:
                return False, {"missing_place": place}
            if container["start"] > ev["start"] or container["end"] < ev["end"]:
                return False, {"event_range": ev}

        allowed = [(d["from"], d["to"]) for d in constraints.get("direct_flights")]
        for a, b in zip(segments, segments[1:]):
            pair = (a["place"], b["place"])
            if pair not in allowed:
                return False, {"flight": {"from": a["place"], "to": b["place"]}}

        return True, {}

    def format_trip_feedback(self, violated_constraints):
        if not violated_constraints:
            return ""
        
        feedback = "\nYour solution violates the following constraints:\n"
        if "total_days" in violated_constraints:
            feedback += f"- The itinerary must cover exactly {violated_constraints['total_days']} days\n"
        if "stay_days" in violated_constraints:
            for place, required_days in violated_constraints["stay_days"].items():
                feedback += f"- Must stay in {place} for exactly {required_days} days\n"
        if "flight" in violated_constraints:
            flight = violated_constraints["flight"]
            feedback += f"- No direct flight available from {flight['from']} to {flight['to']}\n"
        feedback += "\nPlease revise your solution to satisfy these constraints."
        return feedback

    def extract_answer(self, answer_str, task):
        """Extract structured answer from text output using GPT-4.1-nano"""
        try:
            client = OpenAI(api_key=self.keys.get("openai"))
        except (FileNotFoundError, KeyError):
            logging.warning("Could not initialize OpenAI client for answer extraction")
            return {}

        prompt = {
            "calendar": "Given the following time range:\n" + answer_str + "\nExtract the meeting start day and time in a JSON like {\"day\": \"Monday\", \"start_time\": \"14:30\", \"end_time\": \"15:30\"}. The time should be in 24-hour format. If no time range is given at all, output an empty JSON. Do not change the answer whatsoever, just extract the information from the given text.",
            "trip": "Given the following itinerary:\n" + answer_str + "\nExtract the days spent in each city in a JSON format like {\"itinerary\": [{\"day_range\": \"Day 1-2\", \"place\": \"Reykjavik\"}, {\"day_range\": \"Day 2-4\", \"place\": \"Stockholm\"}......]}. Only keep the days in a city. If flying from city A to city B, that day should be included in both ranges for both cites. The day range should be inclusive. For example, arrving at Reykjavik in Day 1 and flying to Stockholm on Day 2 will result in the dictionary above. If no itinerary is given, output an empty JSON. Do not change the answer whatsoever, just extract the information from the given text.",
            "meeting": "Given the following meeting schedule:\n" + answer_str + "\nExtract the complete meeting information in a JSON format like {\"itinerary\": [{\"action\": \"meet\", \"person\": \"David\", \"location\": \"Central Park\", \"start_time\": \"13:00\", \"end_time\": \"14:00\"}, ...]}. Include all fields from the original output including location. The time should be converted to a 24-hour format. If no time range is given at all, output an empty JSON. Do not change the answer whatsoever, just extract the information from the given text."
        }

        try:
            response = client.chat.completions.create(
                model="gpt-4.1-nano",
                messages=[
                    {
                        "role": "user",
                        "content": prompt[task]
                    }
                ],
                response_format={"type": "json_object"},
                temperature=0,
                max_tokens=2000,
                top_p=1
            )
            output_json = response.choices[0].message.content
            logging.info(f"Extracted answer JSON: {output_json}")
            return json.loads(output_json)
        except Exception as e:
            logging.error(f"Error in answer extraction: {e}")
            return {}

    def convert_to_24hr_no_leading_zero(self, time_str):
        """Convert time string to 24-hour format without leading zeros."""
        if not time_str:
            return ""
        
        try:
            # Remove any spaces and make uppercase
            time_str = time_str.strip().replace(" ", "").upper()
            time_part = time_str
            
            # Check for AM/PM
            period = None
            if "AM" in time_str:
                period = "AM"
                time_part = time_str.replace("AM", "")
            elif "PM" in time_str:
                period = "PM"
                time_part = time_str.replace("PM", "")
            
            # Split hours and minutes
            if ":" in time_part:
                hours, minutes = time_part.split(":")
            else:
                hours = time_part
                minutes = "00"
            
            # Convert to integer hours (removes leading zero)
            hours = int(hours)
            
            # Apply 24-hour conversion if period exists
            if period == "PM" and hours != 12:
                hours += 12
            elif period == "AM" and hours == 12:
                hours = 0
            
            # Format without leading zeros
            return f"{hours}:{minutes}"
        
        except Exception as e:
            logging.error(f"Error converting time string '{time_str}': {e}")
            return ""

    def parse_time(self, time_str):
        """Parse time string into datetime.time object"""
        if not time_str:
            return None
        
        # First remove any leading zeros from the hour part
        time_str = self.remove_leading_zeros(time_str)
        
        try:
            if time_str.endswith(("AM", "PM")):
                return datetime.strptime(time_str, "%I:%M%p").time()
            return datetime.strptime(time_str, "%H:%M").time()
        except ValueError:
            return None

    def extract_code(self, response):
        """Extract Python code from model response"""
        response = response.strip()
        
        # First try to extract reasoning (everything before the code)
        code = None
        
        # Look for code delimiters
        delimiters = [
            ("```python", "```"),
            ("```", "```"),
            ("'''python", "'''"),
            ("'''", "'''"),
            ('"""python', '"""'),
            ('"""', '"""')
        ]
        
        for start_delim, end_delim in delimiters:
            start_idx = response.find(start_delim)
            if start_idx != -1:
                start_idx += len(start_delim)
                end_idx = response.find(end_delim, start_idx)
                if end_idx != -1:
                    code = response[start_idx:end_idx].strip()
                    break
        
        # If no delimiters found, try to identify code by Python indicators
        if code is None:
            python_indicators = [
                "#!/usr/bin/env python",
                "if __name__ == \"__main__\":",
                "def main():",
                "import ",
                "from ",
                "print(",
                "def ",
                "class ",
                "return ",
                " = "
            ]
            
            # Try to find where code might start
            for indicator in python_indicators:
                idx = response.find(indicator)
                if idx != -1:
                    code = response[idx:].strip()
                    break
        
        return code

    def run_generated_code(self, code, task):
        """Execute generated Python code and return output"""
        try:
            # Save the exact code to be executed
            filename = f"generated_code_{task}_{current_time}.py"
            with open(filename, "w") as file:
                file.write(code)
            
            start_time = time.time()
            result = subprocess.run(["python", filename], 
                                  capture_output=True, 
                                  text=True, 
                                  check=True)
            exec_time = time.time() - start_time
            output = result.stdout.strip()
            return output, None, exec_time
        except subprocess.CalledProcessError as e:
            exec_time = time.time() - start_time
            # Return the full error message including traceback
            error_message = e.stderr.strip()
            return None, error_message, exec_time
        except Exception as e:
            exec_time = time.time() - start_time
            return None, str(e), exec_time

    def count_tokens(self, text):
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

    async def run_model(self, model_name, prompt):
        """Run the specified model with the given prompt and return timing info"""
        start_time = time.time()
        try:
            # Get a fresh model instance (important for non-DeepSeek models)
            ai = await self.get_model_instance(model_name)
            
            # Use the Kani instance to chat with the model
            await self.rate_limiter.wait()
            response = await ai.chat_round_str(prompt)
            api_time = time.time() - start_time
            
            # Only count tokens for DeepSeek models
            token_count = 0
            if model_name.startswith("DeepSeek"):
                token_count = self.count_tokens(response)
            
            return response, api_time, token_count
        except Exception as e:
            logging.error(f"Error calling model {model_name}: {e}")
            return None, 0, 0

    def save_output_files(self, task, example_id, pass_num, conversation, code, output, evaluation):
        """Save all output files for a given pass"""
        output_dir = f"../output/Python/Qwen-Coder-32B-Instruct/{task}/n_pass/{example_id}/{pass_num}_pass"
        os.makedirs(output_dir, exist_ok=True)
        
        # Save conversation
        with open(f"{output_dir}/conversation.json", "w") as f:
            json.dump(conversation, f, indent=4)
        
        # Save generated code exactly as it appears in the response
        with open(f"{output_dir}/solution.py", "w") as f:
            f.write(code)
        
        # Save execution output
        with open(f"{output_dir}/output.out", "w") as f:
            f.write(output if output else "")
        
        # Save evaluation results
        with open(f"{output_dir}/evaluation.json", "w") as f:
            json.dump(evaluation, f, indent=4)

    async def process_example(self, task, example_id, example_data, model_name, semaphore):
        """Process a single example with multiple passes if needed."""
        async with semaphore:
            config = self.task_config[task]
            constraints = self.constraints[task].get(example_id, {}).get("constraints", {})
            constraints["golden_plan"] = example_data["golden_plan"]  # Add golden plan to constraints
            
            # Initialize conversation history
            conversation = []
            
            # Get initial prompt
            initial_prompt = config["prefix"] + example_data["prompt_0shot"] + config["suffix"]
            current_prompt = initial_prompt
            
            for pass_num in range(1, self.args.max_passes + 1):
                logging.info(f"Processing {task} example {example_id}, pass {pass_num} with {model_name}")
                
                # Get model response with timing
                response_start = time.time()
                response, api_time, token_count = await self.run_model(model_name, current_prompt)
                if not response:
                    logging.error(f"Failed to get response for {example_id}")
                    return
                
                # Add to conversation history
                conversation.append({"role": "user", "content": current_prompt})
                conversation.append({"role": "assistant", "content": response})
                
                # Extract code
                code = self.extract_code(response)
                if not code:
                    logging.warning(f"No code found in response for {example_id}")
                    
                    # Save output files even if no code was found
                    self.save_output_files(
                        task, example_id, pass_num,
                        conversation, response, "",
                        {
                            "error": "No code found in model response",
                            "timing": {
                                "api_call_time": api_time,
                                "token_count": token_count
                            }
                        }
                    )
                    return
                
                # Execute code with timing
                output, error, exec_time = self.run_generated_code(code, task)
                
                # Check for execution errors
                has_execution_error = (error is not None or 
                                      "Error" in (output or "") or 
                                      "Exception" in (output or "") or 
                                      "Traceback" in (output or "") or 
                                      not (output or "").strip())
                
                # Parse output and golden plan with timing
                pred_extract_start = time.time()
                predicted_output = config["parse_output"](output if not has_execution_error else None)
                pred_extract_time = time.time() - pred_extract_start
                
                gold_extract_start = time.time()
                golden_output = config["parse_golden"](example_data["golden_plan"])
                gold_extract_time = time.time() - gold_extract_start
                
                # Evaluate constraints with timing
                constraint_eval_start = time.time()
                constraints_satisfied, violated = config["evaluate"](constraints, predicted_output)
                constraint_eval_time = time.time() - constraint_eval_start
                
                # Check if output matches golden solution
                is_exact_match = predicted_output == golden_output

                # Determine status
                if constraints_satisfied and not has_execution_error:
                    status = "Correct"
                elif has_execution_error:
                    status = "Error"
                else:
                    status = "Wrong plan"
                
                # Prepare evaluation result with new structure
                eval_result = {
                    "has_execution_error": has_execution_error,
                    "execution_output": output if not has_execution_error else error,
                    "pred": predicted_output,
                    "gold": golden_output,
                    "status": status,
                    "violated_constraint": violated,
                    "is_exact_match": is_exact_match,
                    "constraints_satisfied": constraints_satisfied,
                    "pass_number": pass_num,
                    "timing": {
                        "api_call_time": api_time,
                        "execution_time": exec_time,
                        "constraint_eval_time": constraint_eval_time,
                        "pred_extract_time": pred_extract_time,
                        "gold_extract_time": gold_extract_time,
                        "token_count": token_count
                    }
                }
                
                # Save output files
                self.save_output_files(
                    task, example_id, pass_num,
                    conversation, code, output if not has_execution_error else error,
                    eval_result
                )
                
                # Update state
                self.state.update_example(task, example_id, pass_num, constraints_satisfied, is_exact_match)
                self.state.save()
                
                # Check if we're done
                if constraints_satisfied:  # removed the is_exact_match requirement
                    logging.info(f"Successfully solved {task} example {example_id} in pass {pass_num}")
                    return
                
                # Prepare enhanced feedback for next iteration
                feedback_parts = []
                
                if has_execution_error:
                    feedback_parts.append(f"Previous code execution failed with error:\n{error if error else output}")
                    feedback_parts.append(f"\nGenerated code that caused the error:\n```python\n{code}\n```")
                else:
                    feedback_parts.append(f"Previous code produced this output:\n{output}")
                    feedback_parts.append(config["format_feedback"](violated))
                    feedback_parts.append(f"\nGenerated code that produced this output:\n```python\n{code}\n```")
                
                feedback_parts.append("\nPlease carefully review the error/output, the constraints violated, and the code.")
                feedback_parts.append("Revise your solution to fix these issues while maintaining all required functionality.")
                
                current_prompt = "\n".join(feedback_parts)

    async def run(self):
        """Main execution method with parallel processing"""
        tasks_to_run = ["calendar", "meeting", "trip"] if self.args.task == "all" else [self.args.task]
        
        # Create a semaphore to limit concurrent tasks
        semaphore = asyncio.Semaphore(self.args.max_concurrent)
        
        # Create a list to hold all our tasks
        all_tasks = []
        
        for model_name in self.args.model:
            if model_name not in self.engines:
                logging.warning(f"Skipping model {model_name} - not initialized")
                continue
            
            for task in tasks_to_run:
                if task not in self.prompts:
                    logging.warning(f"Skipping task {task} - no prompts loaded")
                    continue
                
                # Update task-specific logging and state for each task when running "all"
                if self.args.task == "all":
                    self.task_name = task
                    self.configure_logging()
                    self.state = EvaluationState(self.task_name)
                    self.state.load()
                
                logging.info(f"Starting {task} task with model {model_name}")
                
                # Process examples
                examples = list(self.prompts[task].items())
                
                # Handle example filtering
                if self.args.examples:
                    # Parse comma-separated example numbers
                    example_numbers = [int(num.strip()) for num in self.args.examples.split(",") if num.strip()]
                    # Filter examples to only include specified numbers
                    task_prefix = "calendar_scheduling" if task == "calendar" else f"{task}_planning"
                    examples = [(f"{task_prefix}_example_{num}", ex) for num in example_numbers 
                              for ex_id, ex in examples if ex_id == f"{task_prefix}_example_{num}"]
                
                end_idx = self.args.end if self.args.end != -1 else len(examples)
                examples_to_process = examples[self.args.start:end_idx]
                
                # Create tasks for all examples
                for example_id, example_data in examples_to_process:
                    # Skip if already successfully processed (unless --fresh)
                    if not self.args.fresh and self.state.is_example_complete(task, example_id):
                        logging.info(f"Skipping already completed {task} example {example_id}")
                        continue
                    
                    # Create task for this example
                    task_obj = asyncio.create_task(
                        self.process_example(task, example_id, example_data, model_name, semaphore)
                    )
                    all_tasks.append(task_obj)
        
        # Wait for all tasks to complete
        await asyncio.gather(*all_tasks)
        
        # Print final statistics
        self.state.print_statistics()

class EvaluationState:
    """Class to track evaluation state across runs"""
    def __init__(self, task_name):
        self.state_file = f"evaluation_state_{task_name}_{current_time}.json"
        self.data = {
            "calendar": {},
            "meeting": {},
            "trip": {}
        }
        self.load()
    
    def load(self):
        try:
            with open(self.state_file, "r") as f:
                loaded = json.load(f)
                self.data = loaded
        except (FileNotFoundError, json.JSONDecodeError):
            pass
    
    def save(self):
        with open(self.state_file, "w") as f:
            json.dump(self.data, f, indent=4)
    
    def update_example(self, task, example_id, pass_num, constraints_satisfied, is_exact_match):
        if example_id not in self.data[task]:
            self.data[task][example_id] = {
                "passes": [],
                "best_pass": None,
                "completed": False
            }
        
        self.data[task][example_id]["passes"].append({
            "pass_number": pass_num,
            "constraints_satisfied": constraints_satisfied,
            "is_exact_match": is_exact_match,
            "timestamp": datetime.now().isoformat()
        })
        
        if constraints_satisfied:
            self.data[task][example_id]["best_pass"] = pass_num
            self.data[task][example_id]["completed"] = True
    
    def is_example_complete(self, task, example_id):
        return self.data.get(task, {}).get(example_id, {}).get("completed", False)
    
    def print_statistics(self):
        print("\n=== Evaluation Statistics ===")
        for task in ["calendar", "meeting", "trip"]:
            if not self.data[task]:
                continue
                
            total = len(self.data[task])
            completed = sum(1 for e in self.data[task].values() if e["completed"])
            exact_matches = sum(
                1 for e in self.data[task].values() 
                if any(p["is_exact_match"] for p in e["passes"])
            )
            
            avg_passes = sum(
                len(e["passes"]) for e in self.data[task].values()
            ) / total
            
            print(f"\n{task.capitalize()} Task:")
            print(f"  Examples: {total}")
            print(f"  Completed: {completed} ({completed/total:.1%})")
            print(f"  Exact matches: {exact_matches} ({exact_matches/total:.1%})")
            print(f"  Average passes per example: {avg_passes:.1f}")

if __name__ == "__main__":
    program = SchedulingProgram()
    asyncio.run(program.run())
