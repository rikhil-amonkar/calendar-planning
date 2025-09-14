"""
Parallel Scheduling Program with Iterative SMT Refinement

This program solves calendar scheduling, meeting planning, and trip planning problems using LLMs
to generate and iteratively refine SMT solutions. It processes multiple examples in parallel
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
from transformers import AutoTokenizer, AutoModelForCausalLM

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
            },
            "zebralogic": {  # New ZebraLogic task config (New Addition)
                "prefix": self.zebralogic_prefix,
                "suffix": self.zebralogic_suffix,
                "parse_golden": self.parse_zebralogic_golden,
                "parse_output": self.parse_zebralogic_output,
                "evaluate": self.evaluate_zebralogic,
                "format_feedback": self.format_zebralogic_feedback
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
  
  # Force re-run all examples (ignore existing results)
  python scheduling_program.py --task meeting --model DeepSeek-R1 --fresh
  
  # Run with parallel processing (10 concurrent examples)
  python scheduling_program.py --task trip --model DeepSeek-V3 --max_concurrent 10 --rate_limit 5

  # Run ZebraLogic puzzles with DeepSeek-V3 on examples 0-4
  python scheduling_program.py --task zebralogic --model DeepSeek-V3 --start 0 --end 5

  # Run all tasks with multiple models, max 3 passes per example
  python scheduling_program.py --task all --model DeepSeek-V3 gpt-4o-mini --max_passes 3
"""
        )
        parser.add_argument('--task', choices=['calendar', 'trip', 'meeting', 'zebralogic', 'all'], required=True,
                          help="Task to run: calendar, trip, meeting, zebralogic, or all")
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
        parser.add_argument('--api_key_file', type=str, default='../../openai_research/ai2_openai_key.json',
                          help="Path to file containing API keys")
        parser.add_argument('--examples', type=str,
                          help="Comma-separated list of specific example numbers to run")
        return parser.parse_args()

    def setup_directories(self):
        """Ensure all required directories exist"""
        os.makedirs("output", exist_ok=True)
        for task in ["calendar", "meeting", "trip", "zebralogic"]:  # New ZebraLogic directory (New Addition)
            os.makedirs(f"output/{task}", exist_ok=True)

    def initialize_models(self):
        """Initialize all requested models and check Z3 availability"""
        try:
            with open(self.args.api_key_file) as f:
                self.keys = json.load(f)
        except FileNotFoundError:
            logging.error(f"API key file {self.args.api_key_file} not found")
            sys.exit(1)
        except json.JSONDecodeError:
            logging.error(f"Invalid JSON in API key file {self.args.api_key_file}")
            sys.exit(1)

        # Check if Z3 is needed and available
        if any(task in self.args.task for task in ["calendar", "all"]):
            try:
                import z3
                logging.info("Z3 solver is available")
            except ImportError:
                logging.warning("Z3 solver not found. Will attempt to install when needed.")

        self.engines = {}
        HF_CACHE_DIR = "/local-ssd/rma336/.cache/huggingface"

        for model_name in self.args.model:
            try:
                if model_name.startswith("DeepSeek"):
                    self.engines[model_name] = OpenAIEngine(
                        api_key=self.keys.get("deepseek"),
                        model="deepseek-chat" if model_name == "DeepSeek-V3" else "deepseek-reasoner",
                        api_base="https://api.deepseek.com",
                        max_context_size=50000
                    )

                elif model_name.startswith(("gpt", "o3", "o4")):
                    self.engines[model_name] = OpenAIEngine(
                        api_key=self.keys.get("openai"),
                        model=model_name,
                        # reasoning_effort="high"  # Reasoning effort for o3-mini --> gpt-5-2025-08-07
                    )

                else:
                    # ---- Hugging Face model (e.g., Qwen) ----
                    model_id = model_name
                    HF_CACHE_DIR = "/local-ssd/rma336/.cache/huggingface"

                    tok = AutoTokenizer.from_pretrained(
                        model_id,
                        cache_dir=HF_CACHE_DIR,
                        trust_remote_code=True,
                    )
                    mdl = AutoModelForCausalLM.from_pretrained(
                        model_id,
                        cache_dir=HF_CACHE_DIR,
                        device_map="auto",
                        torch_dtype="auto",
                        trust_remote_code=True,
                    )

                    # Qwen/Qwen3: set pad token + left padding
                    if tok.pad_token_id is None:
                        tok.pad_token = tok.eos_token
                    tok.padding_side = "left"
                    mdl.config.pad_token_id = tok.pad_token_id
                    mdl.eval()

                    # IMPORTANT: construct engine WITHOUT 'model=' to avoid leaking it into model_kwargs
                    engine = HuggingEngine(model_id=model_id)

                    # Attach preloaded model + tokenizer
                    engine.model = mdl
                    engine.tokenizer = tok

                    # (Paranoia) remove any stray 'model' kwarg Kani might forward to generate()
                    if hasattr(engine, "model_kwargs"):
                        engine.model_kwargs.pop("model", None)

                    # Ensure attention_mask is produced & sensible gen defaults
                    engine.encode_kwargs = {
                        "padding": True,
                        "truncation": True,
                        "return_tensors": "pt",
                    }
                    gen = getattr(engine, "generation_kwargs", {}) or {}
                    gen.setdefault("pad_token_id", tok.pad_token_id)
                    gen.setdefault("eos_token_id", tok.eos_token_id)
                    gen.setdefault("max_new_tokens", 512)
                    gen.setdefault("do_sample", False)
                    gen.setdefault("temperature", 0.0)
                    engine.generation_kwargs = gen

                    self.engines[model_name] = engine

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

        # ZebraLogic data (New JSON-based loading)
        try:
            with open("../data/zebralogic_sample_100.json") as f:
                zebra_data = json.load(f)
                
            self.prompts["zebralogic"] = {}
            self.constraints["zebralogic"] = {}
            
            for example_id, example in zebra_data.items():
                self.prompts["zebralogic"][example_id] = {
                    "prompt_0shot": example["prompt_0shot"],
                    "golden_plan": example["golden_plan"]
                }
                self.constraints["zebralogic"][example_id] = {
                    "constraints": {
                        "golden_plan": example["golden_plan"],
                        "meta": example.get("meta", {})
                    }
                }
                
        except Exception as e:
            logging.warning(f"Failed to load ZebraLogic data: {e}")

    # Task-specific prompt components - UPDATED FOR SMT
    @property
    def calendar_prefix(self):
        return (
            "You are an expert at scheduling meetings using SMT solvers. Your task is to find a suitable time for a meeting "
            "based on the participants' schedules and constraints using the Z3 SMT solver. In this case:\n"
        )

    @property
    def calendar_suffix(self):
        return (
            "\nGenerate a fully working Python script with Z3 SMT code that calculates a proposed time and outputs it in the format HH:MM:HH:MM. "
            "The script should also output the day of the week (e.g., Monday, Tuesday). "
            "The script should be clean, well-formatted, and enclosed within ```python and ```. "
            "The output of the generated code must include both the time range (like {14:30:15:30}) and the day of the week. "
            "Provide the response with only code."
        )

    @property
    def meeting_prefix(self):
        return (
            "You are an expert computational meeting planner using SMT solvers. Your task is to write a Python program that "
            "algorithmically calculates the optimal meeting schedule based on the participants' constraints using the Z3 SMT solver.\n"
            "The program must actually compute the plan using SMT constraints with the given parameters, not just print a pre-determined answer.\n"
            "Input parameters:\n"
        )

    @property
    def meeting_suffix(self):
        return (
            "\n\nGenerate a complete, self-contained Python program using Z3 SMT solver that:\n"
            "1. Takes the above meeting constraints as input variables\n"
            "2. Computes the optimal meeting schedule using SMT logical rules and constraints\n"
            "3. Outputs the result as a JSON-formatted dictionary with the following structure:\n"
            "{\n"
            '  "itinerary": [\n'
            '    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"},\n'
            '    {"action": "meet", "location": "Location Name", "person": "Person Name", "start_time": "H:MM", "end_time": "H:MM"}\n'
            "  ]\n"
            "}\n"
            "Rules for the program:\n"
            "- Times should be in 24-hour format like '9:00' or '13:30' (no leading zero)\n"
            "- The schedule must account for all travel times and constraints using SMT\n"
            "- The program must actually compute the schedule using Z3, not just print a static answer\n"
            "\n"
            "Output only the complete Python code with Z3 SMT solver with no additional text or explanation.\n"
            "The code must run independently and output valid JSON when executed."
            "The script should be clean, well-formatted, and enclosed within ```python and ```. "
        )

    @property
    def trip_prefix(self):
        return (
            "You are an expert computational trip planner using SMT solvers.\n"
            "Your task is to write a Python program that algorithmically calculates the optimal itinerary based on the participants' constraints using the Z3 SMT solver.\n"
            "The program must actually compute the plan using SMT constraints with the given parameters, not just print a predetermined answer.\n"
        )

    @property
    def trip_suffix(self):
        return (
            "\n\nGenerate a complete, self-contained Python program using Z3 SMT solver that:\n"
            "1. Takes the above trip constraints as input variables\n"
            "2. Computes the optimal itinerary using SMT logical rules and constraints\n"
            "3. Outputs the result as a JSON-formatted dictionary with an 'itinerary' key containing a list of day-place mappings.\n"
            "Example structure of output from running code: {\"itinerary\": [{\"day_range\": \"Day 1-5\", \"place\": \"Helsinki\"}, {\"day_range\": \"Day 5-9\", \"place\": \"Barcelona\"}, {\"day_range\": \"Day 9-14\", \"place\": \"Florence\"}]}\n"
            "Note that the JSON structure should be what the Python program outputs, not just a string representation.\n"
            "4. Note that if one flies from city A to city B on day X, then they are in both cities A and B on day X, which contributes to the total number of days in each city.\n"
            "The program must include:\n"
            "- Actual SMT calculations to determine durations and transitions\n"
            "Output only the complete Python code with Z3 SMT solver with no additional text or explanation.\n"
            "The code must run independently and output valid JSON when executed."
            "The script should be clean, well-formatted, and enclosed within ```python and ```. "
        )

    # ZebraLogic Prompt Info Below (New Addition) - UPDATED FOR SMT
    @property
    def zebralogic_prefix(self):
        return (
            "You are an expert at solving Zebra logic puzzles using SMT solvers. Your task is to write a Python program that "
            "algorithmically solves the given logic puzzle by implementing all constraints and rules using the Z3 SMT solver. "
            "The program must actually compute the solution using SMT constraints with the given parameters, not just print a pre-determined answer.\n"
            "Input puzzle:\n"
        )

    @property
    def zebralogic_suffix(self):
        return (
            "\n\nGenerate a complete, self-contained Python program using Z3 SMT solver that:\n"
            "1. Takes the above puzzle constraints as input variables\n"
            "2. Computes the solution using SMT logical rules and constraints\n"
            "3. Outputs the solution as a JSON-formatted dictionary with the following EXACT structure:\n"
            "{\n"
            '  "solution": {\n'
            '    "header": [GOLDEN_HEADERS_PLACEHOLDER],\n'
            '    "rows": [\n'
            '      ["1", VALUE_FOR_HEADER1, VALUE_FOR_HEADER2, ...],\n'
            '      ["2", VALUE_FOR_HEADER1, VALUE_FOR_HEADER2, ...]\n'
            '    ]\n'
            "  }\n"
            "}\n"
            "\n"
            "Important Requirements:\n"
            "- The 'header' field MUST use exactly these attribute names: [GOLDEN_HEADERS_PLACEHOLDER]\n"
            "- Maintain the exact order of houses (1, 2, 3, ...)\n"
            "- Include all attributes in each row\n"
            "- The output must be valid JSON that can be parsed by Python's json module\n"
            "\n"
            "Output only the complete Python code with Z3 SMT solver with no additional text or explanation.\n"
            "The code must run independently and output valid JSON when executed."
            "The script should be clean, well-formatted, and enclosed within ```python and ```. "
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

    # Task-specific parsing and evaluation methods - UPDATED FOR SMT
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
        """Parse SMT model output into structured format"""
        if not output:
            return None
        
        # First try to extract from SMT output format
        day_match = re.search(r'Day:\s*([A-Za-z]+)', output, re.IGNORECASE)
        time_match = re.search(r'Time:\s*\{(\d{1,2}:\d{2}):(\d{1,2}:\d{2})\}', output, re.IGNORECASE)
        
        if day_match and time_match:
            day = day_match.group(1)
            start_time = self.remove_leading_zeros(time_match.group(1))
            end_time = self.remove_leading_zeros(time_match.group(2))
            time_output = f"{{{start_time}:{end_time}}}"
            
            return {
                "day": day,
                "time_range": time_output
            }
        
        # Fallback to GPT extraction
        try:
            extracted = self.extract_answer(output, "calendar")
            if extracted and "day" in extracted and "start_time" in extracted and "end_time" in extracted:
                start_time = self.remove_leading_zeros(extracted['start_time'])
                end_time = self.remove_leading_zeros(extracted['end_time'])
                time_output = f"{{{start_time}:{end_time}}}"
                return {
                    "day": extracted["day"],
                    "time_range": time_output
                }
        except Exception as e:
            logging.warning(f"Error extracting answer: {e}")
        
        return None

    def evaluate_calendar(self, constraints, predicted_output):
        """Evaluate calendar constraints with SMT-specific handling"""
        if not predicted_output:
            return False, {"missing_output": True}
        
        # Handle Z3 errors specifically
        if isinstance(predicted_output, dict):
            if "z3_error" in predicted_output:
                return False, {"z3_error": predicted_output["z3_error"]}
            if "no_solution" in predicted_output:
                return False, {"no_solution": True}
            if "error" in predicted_output:
                return False, {"execution_error": predicted_output["error"]}
        
        # Normal evaluation for successful outputs
        if not isinstance(predicted_output, dict) or "day" not in predicted_output or "time_range" not in predicted_output:
            return False, {"invalid_format": True}

        predicted_day = predicted_output["day"]
        predicted_time = predicted_output["time_range"]
        
        # Convert time strings to numerical values
        try:
            time_parts = predicted_time.strip("{}").split(":")
            if len(time_parts) == 4:  # HH:MM:HH:MM format
                start_parts = time_parts[0:2]
                end_parts = time_parts[2:4]
            else:  # Assume HH:MM-HH:MM format
                time_range = predicted_time.strip("{}")
                if "-" in time_range:
                    start_parts, end_parts = time_range.split("-")
                    start_parts = start_parts.split(":")
                    end_parts = end_parts.split(":")
                else:
                    return False, {"unparsable_time": predicted_time}
            
            pred_start = float(start_parts[0]) + float(start_parts[1]) / 60
            pred_end = float(end_parts[0]) + float(end_parts[1]) / 60
        except (ValueError, IndexError):
            return False, {"unparsable_time": predicted_time}

        meeting_duration = constraints.get("meeting_duration", 0)
        if abs((pred_end - pred_start) - meeting_duration) > 0.01:  # Allow small floating point errors
            return False, {"meeting_duration": f"expected {meeting_duration}, got {pred_end - pred_start:.2f}"}

        for disallowed_range in constraints.get("disallowed_ranges", []):
            if disallowed_range["day"].lower() == predicted_day.lower():
                if (pred_start >= disallowed_range["start"] and pred_start < disallowed_range["end"]) or \
                        (pred_end > disallowed_range["start"] and pred_end <= disallowed_range["end"]) or \
                        (pred_start <= disallowed_range["start"] and pred_end >= disallowed_range["end"]):
                    return False, disallowed_range
        return True, {}

    def format_calendar_feedback(self, violated_constraints):
        if not violated_constraints:
            return ""
        
        feedback = "\nYour solution has the following issues:\n"
        
        if "z3_error" in violated_constraints:
            feedback += f"- Z3 solver error: {violated_constraints['z3_error']}\n"
            feedback += "- Please ensure your code properly imports and uses the z3 module\n"
        elif "no_solution" in violated_constraints:
            feedback += "- The constraints appear to be unsatisfiable (no solution found)\n"
            feedback += "- Please check if the constraints are too restrictive\n"
        elif "execution_error" in violated_constraints:
            feedback += f"- Execution error: {violated_constraints['execution_error']}\n"
        elif "meeting_duration" in violated_constraints:
            feedback += f"- The meeting duration must be exactly {violated_constraints['meeting_duration']} hours\n"
        elif "day" in violated_constraints and "start" in violated_constraints:
            feedback += f"- The meeting time conflicts with an unavailable time slot on {violated_constraints['day']} from {violated_constraints['start']} to {violated_constraints['end']}\n"
        elif "unparsable_time" in violated_constraints:
            feedback += f"- Could not parse the time format: {violated_constraints['unparsable_time']}\n"
            feedback += "- Please output time in format: {{HH:MM:HH:MM}} or Day: Monday, Time: {{14:30:15:30}}\n"
        
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

    # New parsing and extraction of ZebraLogic (New Addition)
    def parse_zebralogic_golden(self, golden_plan):
        """Parse the golden solution into a structured format."""
        if not isinstance(golden_plan, dict) or "rows" not in golden_plan:
            return {"error": "Invalid golden plan format"}
        
        # Convert the table format to a list of dicts
        solution = []
        headers = golden_plan["header"]
        for row in golden_plan["rows"]:
            solution.append(dict(zip(headers, row)))
        return solution

    def parse_zebralogic_output(self, output, golden_headers=None):
        """Parse model output into structured format: list[dict] per house."""
        if not output:
            return None

        try:
            # First try to extract structured answer using GPT-4.1-nano
            try:
                extracted = self.extract_answer(output, "zebralogic", golden_headers)
                if extracted and "solution" in extracted:
                    solution = extracted["solution"]
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
                logging.warning(f"Error extracting answer with GPT-4.1-nano: {e}")

            # Fall back to original parsing if extraction fails
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

    def evaluate_zebralogic(self, constraints, predicted_output):
        """Evaluate ZebraLogic solution with more robust comparison"""
        if not predicted_output or not isinstance(predicted_output, list):
            return False, {"invalid_output": "No valid output structure found"}
        
        golden_output = self.parse_zebralogic_golden(constraints.get("golden_plan", {}))
        
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

    def format_zebralogic_feedback(self, violated_constraints):
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

    def extract_answer(self, answer_str, task, golden_headers=None):
        """Extract structured answer from text output using GPT-4.1-nano"""
        try:
            client = OpenAI(api_key=self.keys.get("openai"))
        except (FileNotFoundError, KeyError):
            logging.warning("Could not initialize OpenAI client for answer extraction")
            return {}

        # Use provided golden_headers or default to empty list
        if golden_headers is None:
            golden_headers = []
        
        header_placeholder = json.dumps(golden_headers)

        prompt = {
            "calendar": "Given the following time range:\n" + answer_str + "\nExtract the meeting start day and time in a JSON like {\"day\": \"Monday\", \"start_time\": \"14:30\", \"end_time\": \"15:30\"}. The time should be in 24-hour format. If no time range is given at all, output an empty JSON. Do not change the answer whatsoever, just extract the information from the given text.",
            "trip": "Given the following itinerary:\n" + answer_str + "\nExtract the days spent in each city in a JSON format like {\"itinerary\": [{\"day_range\": \"Day 1-2\", \"place\": \"Reykjavik\"}, {\"day_range\": \"Day 2-4\", \"place\": \"Stockholm\"}......]}. Only keep the days in a city. If flying from city A to city B, that day should be included in both ranges for both cites. The day range should be inclusive. For example, arrving at Reykjavik in Day 1 and flying to Stockholm on Day 2 will result in the dictionary above. If no itinerary is given, output an empty JSON. Do not change the answer whatsoever, just extract the information from the given text.",
            "meeting": "Given the following meeting schedule:\n" + answer_str + "\nExtract the complete meeting information in a JSON format like {\"itinerary\": [{\"action\": \"meet\", \"person\": \"David\", \"location\": \"Central Park\", \"start_time\": \"13:00\", \"end_time\": \"14:00\"}, ...]}. Include all fields from the original output including location. The time should be converted to a 24-hour format. If no time range is given at all, output an empty JSON. Do not change the answer whatsoever, just extract the information from the given text.",
            "zebralogic": (
                "Given the following puzzle solution:\n" + answer_str + 
                "\nExtract the solution in a JSON format that exactly matches the expected output structure. "
                "The JSON must contain these exact headers: " + header_placeholder + ". "
                "Example of required format:\n"
                "{\n"
                '  "solution": {\n'
                '    "header": ' + header_placeholder + ',\n'
                '    "rows": [\n'
                '      ["1", VALUE_FOR_HEADER1, VALUE_FOR_HEADER2, ...],\n'
                '      ["2", VALUE_FOR_HEADER1, VALUE_FOR_HEADER2, ...]\n'
                '    ]\n'
                "  }\n"
                "}\n\n"
                "Important:\n"
                "- Keep all original values exactly as provided\n"
                "- The header names MUST match exactly: " + header_placeholder + "\n"
                "- Maintain correct house ordering (1, 2, 3...)\n"
                "- Include all attributes in each row\n"
                "- If no valid solution is given, output empty JSON {}\n"
                "- Do not include any explanatory text, only the JSON"
            )
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

    # NEW SMT-SPECIFIC METHODS FROM SECOND CODE
    def smart_extract_code(self, response_txt):
        """
        Smart code extraction using GPT when traditional regex fails
        """
        # First try traditional regex extraction
        matches = re.findall(r"```python\s*(.*?)```", response_txt, re.DOTALL)
        if matches:
            return matches[-1].strip()
        
        # If no code blocks found, try to extract code using GPT
        client = self.get_openai_client()
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

    def smart_extract_execution_result(self, execution_output, task):
        """Smart extraction of execution results with Z3-specific handling"""
        if not execution_output:
            return {"error": "No output"}
        
        # Check for Z3-specific errors
        z3_errors = [
            "ModuleNotFoundError: No module named 'z3'",
            "z3.z3types.Z3Exception",
            "NameError: name 'z3' is not defined",
            "ImportError"
        ]
        
        for error in z3_errors:
            if error in execution_output:
                return {"z3_error": "Z3 solver not properly installed or imported"}
        
        # Use the existing extraction logic but with Z3 awareness
        client = self.get_openai_client()
        if not client:
            return self.extract_answer_basic(execution_output, task)
        
        try:
            prompt = f"""Extract structured data from Z3 SMT solver output for a calendar scheduling task.

    Execution Output:
    {execution_output}

    Expected format for successful solution: 
    Day: Monday, Time: {{14:30:15:30}}

    Expected format for errors:
    {{"error": "error_message"}}

    Instructions:
    1. If the output contains a valid day and time in the format above, extract it as JSON
    2. If the output contains Z3 errors or import issues, return {{"z3_error": "description"}}
    3. If the output indicates no solution (unsat), return {{"no_solution": true}}
    4. For other errors, return {{"error": "description"}}

    Return only valid JSON:"""

            response = client.chat.completions.create(
                model="gpt-4o-mini",
                messages=[{"role": "user", "content": prompt}],
                response_format={"type": "json_object"},
                temperature=0,
                max_tokens=1000
            )
            
            return json.loads(response.choices[0].message.content)
            
        except Exception as e:
            logging.error(f"Error in smart execution result extraction: {e}")
            return self.extract_answer_basic(execution_output, task)

    def extract_answer_basic(self, answer_str, task):
        """Basic extraction fallback"""
        try:
            client = OpenAI(api_key=self.keys.get("openai"))
        except (FileNotFoundError, KeyError):
            logging.warning("Could not initialize OpenAI client for answer extraction")
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
            logging.error(f"Error in answer extraction: {e}")
            return {}

    def get_openai_client(self):
        """Get OpenAI client for GPT-based extraction"""
        try:
            return OpenAI(api_key=self.keys.get("openai"))
        except (FileNotFoundError, KeyError):
            logging.warning("Could not initialize OpenAI client for extraction")
            return None

    def execute_python_code(self, code_path):
        """Execute Python code and return the output"""
        try:
            result = subprocess.run(['python3', code_path], capture_output=True, text=True, timeout=30)
            return result.stdout + result.stderr
        except subprocess.TimeoutExpired:
            return "Execution timeout"
        except Exception as e:
            return f"Execution error: {str(e)}"

    def extract_code(self, response):
        """Extract Python code from model response using smart extraction"""
        response = response.strip()
        
        # Use smart extraction first
        code = self.smart_extract_code(response)
        if code:
            return code
        
        # Fall back to basic extraction if smart extraction fails
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

    def execute_python_code(self, code_path):
        """Execute Python code and return the output with proper Z3 handling"""
        try:
            # Install z3-solver if not present
            try:
                import z3
            except ImportError:
                subprocess.run([sys.executable, "-m", "pip", "install", "z3-solver"], 
                            capture_output=True, check=True)
            
            result = subprocess.run([sys.executable, code_path], 
                                capture_output=True, text=True, timeout=30)
            
            # Combine stdout and stderr for better error reporting
            output = result.stdout.strip()
            if result.stderr:
                output += "\n" + result.stderr.strip()
                
            return output
        except subprocess.TimeoutExpired:
            return "Execution timeout"
        except Exception as e:
            return f"Execution error: {str(e)}"

    def run_generated_code(self, code, task):
        """Execute generated Python code and return output with Z3 support"""
        try:
            # Save the exact code to be executed
            filename = f"generated_code_{task}_{int(time.time())}.py"
            with open(filename, "w") as file:
                file.write(code)
            
            start_time = time.time()
            output = self.execute_python_code(filename)
            exec_time = time.time() - start_time
            
            # Clean up the generated file
            try:
                os.remove(filename)
            except:
                pass
                
            return output, None, exec_time
        except Exception as e:
            exec_time = time.time() - start_time if 'start_time' in locals() else 0
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
        """Run the specified model with the given prompt and return timing info and reasoning content"""
        start_time = time.time()
        try:
            # Get a fresh model instance (important for non-DeepSeek models)
            ai = await self.get_model_instance(model_name)
            
            # Use the Kani instance to chat with the model
            await self.rate_limiter.wait()
            
            # Use chat_round instead of chat_round_str to get the full message object
            message = await ai.chat_round(prompt)
            response = message.text if hasattr(message, 'text') else str(message)
            api_time = time.time() - start_time
            
            # Extract reasoning content for DeepSeek models
            reasoning_content = ""
            reasoning_tokens = 0
            
            if model_name.startswith("DeepSeek"):
                # Method 1: Try to get raw reasoning content from message object
                if hasattr(message, 'reasoning_content') and message.reasoning_content:
                    reasoning_content = message.reasoning_content
                    logging.info(f"Found reasoning_content in message object: {len(reasoning_content)} chars")
                
                # Method 2: Extract content between <think> tags (DeepSeek reasoning format)
                if not reasoning_content:
                    think_pattern = r'<think>(.*?)</think>'
                    think_matches = re.findall(think_pattern, response, re.DOTALL)
                    if think_matches:
                        reasoning_content = "\n".join(think_matches).strip()
                        logging.info(f"Extracted reasoning from <think> tags: {len(reasoning_content)} chars")
                
                # Method 3: Look for reasoning text before code blocks
                if not reasoning_content:
                    # Try to extract everything before the first code block
                    code_pattern = r'```(?:python)?\s*\n'
                    code_match = re.search(code_pattern, response)
                    if code_match:
                        reasoning_content = response[:code_match.start()].strip()
                        if reasoning_content and len(reasoning_content) > 50:  # Only use if substantial content
                            logging.info(f"Extracted reasoning before code: {len(reasoning_content)} chars")
                        else:
                            reasoning_content = ""
                
                # Count tokens for both full response and reasoning content
                full_token_count = self.count_tokens(response)
                reasoning_tokens = self.count_tokens(reasoning_content) if reasoning_content else 0
                
            else:
                # For non-DeepSeek models, use character count as fallback
                full_token_count = len(response)
                reasoning_tokens = 0
            
            return response, api_time, full_token_count, reasoning_content, reasoning_tokens
        except Exception as e:
            logging.error(f"Error calling model {model_name}: {e}")
            return None, 0, 0, "", 0

    def save_output_files(self, task, example_id, pass_num, conversation, code, output, evaluation):
        """Save all output files for a given pass"""
        output_dir = f"../output/SMT/Qwen3-32B/{task}/n_pass_noconfeed_2/{example_id}/{pass_num}_pass"
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
        
        # Save evaluation results (ensure token data is included)
        evaluation_with_tokens = evaluation.copy()
        if "timing" not in evaluation_with_tokens:
            evaluation_with_tokens["timing"] = {}
        evaluation_with_tokens["timing"].setdefault("total_tokens", 0)
        evaluation_with_tokens["timing"].setdefault("reasoning_tokens", 0)
        
        # Ensure reasoning content is properly included
        if "reasoning_content" not in evaluation_with_tokens and evaluation.get("reasoning_content"):
            evaluation_with_tokens["reasoning_content"] = evaluation["reasoning_content"]
        
        with open(f"{output_dir}/evaluation.json", "w") as f:
            json.dump(evaluation_with_tokens, f, indent=4)
        
        # Also save reasoning content separately if it exists
        reasoning_content = evaluation.get("reasoning_content")
        if reasoning_content:
            with open(f"{output_dir}/reasoning.txt", "w") as f:
                f.write(reasoning_content)
            
            # Save the full raw response for debugging
            full_response = None
            for msg in conversation:
                if msg.get("role") == "assistant" and "content" in msg:
                    full_response = msg["content"]
                    break
            
            if full_response:
                with open(f"{output_dir}/full_response.txt", "w") as f:
                    f.write(full_response)

    def calculate_token_statistics(self):
        """Calculate and display token usage statistics across all examples"""
        token_data = {
            "calendar": {"total_tokens": 0, "reasoning_tokens": 0, "count": 0},
            "meeting": {"total_tokens": 0, "reasoning_tokens": 0, "count": 0},
            "trip": {"total_tokens": 0, "reasoning_tokens": 0, "count": 0},
            "zebralogic": {"total_tokens": 0, "reasoning_tokens": 0, "count": 0},
            "overall": {"total_tokens": 0, "reasoning_tokens": 0, "count": 0}
        }
        
        # Scan all evaluation files to collect token data
        for task in ["calendar", "meeting", "trip", "zebralogic"]:
            task_dir = f"../output/SMT/Qwen3-32B/{task}/n_pass_noconfeed_2"
            if not os.path.exists(task_dir):
                continue
                
            for example_id in os.listdir(task_dir):
                example_dir = os.path.join(task_dir, example_id)
                if not os.path.isdir(example_dir):
                    continue
                    
                for pass_dir in os.listdir(example_dir):
                    if pass_dir.endswith("_pass") and os.path.isdir(os.path.join(example_dir, pass_dir)):
                        eval_file = os.path.join(example_dir, pass_dir, "evaluation.json")
                        if os.path.exists(eval_file):
                            try:
                                with open(eval_file, 'r') as f:
                                    eval_data = json.load(f)
                                    if "timing" in eval_data:
                                        token_data[task]["total_tokens"] += eval_data["timing"].get("total_tokens", 0)
                                        token_data[task]["reasoning_tokens"] += eval_data["timing"].get("reasoning_tokens", 0)
                                        token_data[task]["count"] += 1
                                        
                                        token_data["overall"]["total_tokens"] += eval_data["timing"].get("total_tokens", 0)
                                        token_data["overall"]["reasoning_tokens"] += eval_data["timing"].get("reasoning_tokens", 0)
                                        token_data["overall"]["count"] += 1
                            except Exception as e:
                                logging.warning(f"Error reading evaluation file {eval_file}: {e}")
        
        # Print statistics
        print("\n=== Token Usage Statistics ===")
        for task in ["calendar", "meeting", "trip", "zebralogic", "overall"]:
            if token_data[task]["count"] > 0:
                avg_total = token_data[task]["total_tokens"] / token_data[task]["count"]
                avg_reasoning = token_data[task]["reasoning_tokens"] / token_data[task]["count"]
                reasoning_percentage = (avg_reasoning / avg_total * 100) if avg_total > 0 else 0
                
                print(f"\n{task.capitalize()}:")
                print(f"  Examples processed: {token_data[task]['count']}")
                print(f"  Average total tokens per response: {avg_total:.1f}")
                print(f"  Average reasoning tokens per response: {avg_reasoning:.1f}")
                print(f"  Reasoning percentage: {reasoning_percentage:.1f}%")

    async def process_example(self, task, example_id, example_data, model_name, semaphore):
        """Process a single example with multiple passes if needed, with Z3-specific handling."""
        async with semaphore:
            config = self.task_config[task]
            
            # ----- FIXED CONSTRAINTS HANDLING -----
            container = self.constraints.get(task, {}).get(example_id, {})
            constraints = container.get("constraints", {})
            if not isinstance(constraints, dict):
                constraints = {}
            constraints.setdefault("golden_plan", example_data.get("golden_plan"))
            # ---------------------------------------
            
            # Initialize conversation history
            conversation = []
            
            # Get initial prompt
            golden_plan = constraints.get("golden_plan", {})
            if task == "zebralogic":
                golden_headers = golden_plan.get("header", [])
            else:
                # For other tasks like meeting, calendar, trip that don't use headers
                golden_headers = []            
            header_placeholder = json.dumps(golden_headers)

            # Replace the placeholder with actual headers
            suffix_with_headers = config["suffix"].replace("[GOLDEN_HEADERS_PLACEHOLDER]", header_placeholder)
            initial_prompt = config["prefix"] + example_data["prompt_0shot"] + suffix_with_headers         
            current_prompt = initial_prompt
            
            # Z3 SPECIFIC: Ensure Z3 is available before processing SMT tasks
            if task == "calendar":
                try:
                    # Test Z3 availability
                    result = subprocess.run([sys.executable, "-c", "import z3; print('Z3 available')"], 
                                        capture_output=True, text=True, timeout=10)
                    if result.returncode != 0:
                        logging.warning("Z3 not available, attempting to install...")
                        try:
                            install_result = subprocess.run([sys.executable, "-m", "pip", "install", "z3-solver"], 
                                                        capture_output=True, text=True, timeout=120)
                            if install_result.returncode == 0:
                                logging.info("Z3 installed successfully")
                            else:
                                logging.error(f"Failed to install Z3: {install_result.stderr}")
                                # Save error state and skip this example
                                self.save_output_files(
                                    task, example_id, 1, [], "", f"Z3 installation failed: {install_result.stderr}",
                                    {
                                        "error": "Z3 not available", 
                                        "status": "Error",
                                        "z3_installation_error": install_result.stderr
                                    }
                                )
                                return
                        except Exception as e:
                            logging.error(f"Failed to install Z3: {e}")
                            self.save_output_files(
                                task, example_id, 1, [], "", f"Z3 installation failed: {e}",
                                {"error": "Z3 installation failed", "status": "Error"}
                            )
                            return
                except Exception as e:
                    logging.error(f"Z3 check failed: {e}")
                    self.save_output_files(
                        task, example_id, 1, [], "", f"Z3 check failed: {e}",
                        {"error": "Z3 check failed", "status": "Error"}
                    )
                    return
                    
            for pass_num in range(1, self.args.max_passes + 1):
                logging.info(f"Processing {task} example {example_id}, pass {pass_num} with {model_name}")
                
                # Get model response with timing and reasoning info
                response_start = time.time()
                response, api_time, full_token_count, reasoning_content, reasoning_tokens = await self.run_model(model_name, current_prompt)
                if not response:
                    logging.error(f"Failed to get response for {example_id}")
                    # Save error state
                    self.save_output_files(
                        task, example_id, pass_num,
                        conversation, "", "No response from model",
                        {
                            "error": "No response from model",
                            "status": "Error",
                            "timing": {
                                "api_call_time": api_time,
                                "total_tokens": full_token_count
                            }
                        }
                    )
                    return

                logging.info(f"Full response received: {len(response)} characters")
                if reasoning_content:
                    logging.info(f"Reasoning content extracted: {len(reasoning_content)} characters")
                
                # Add to conversation history
                conversation.append({"role": "user", "content": current_prompt})
                conversation.append({
                    "role": "assistant", 
                    "content": response,
                    "reasoning_content": reasoning_content,
                    "reasoning_tokens": reasoning_tokens,
                    "total_tokens": full_token_count
                })
                
                # Extract code using smart extraction
                code = self.extract_code(response)
                if not code:
                    logging.warning(f"No code found in response for {example_id}")
                    
                    # Save output files even if no code was found
                    self.save_output_files(
                        task, example_id, pass_num,
                        conversation, response, "",
                        {
                            "error": "No code found in model response",
                            "status": "Error",
                            "timing": {
                                "api_call_time": api_time,
                                "total_tokens": full_token_count,
                                "reasoning_tokens": reasoning_tokens
                            },
                            "reasoning_content": reasoning_content
                        }
                    )
                    # Continue to next pass for refinement
                    current_prompt = "Your previous response did not contain any executable Python code. Please generate a complete Python program that solves the problem."
                    continue
                
                # Execute code with timing
                output, error, exec_time = self.run_generated_code(code, task)
                
                # Z3 SPECIFIC: Enhanced error detection for SMT
                has_execution_error = False
                execution_output = output if not error else error
                
                # Check for various error types
                if error is not None:
                    has_execution_error = True
                elif any(err in (output or "") for err in ["Error", "Exception", "Traceback", "ModuleNotFoundError", "ImportError"]):
                    has_execution_error = True
                elif not (output or "").strip():
                    has_execution_error = True
                elif "unsat" in (output or "").lower() and "sat" not in (output or "").lower():
                    # Z3 specific: unsat means no solution found
                    has_execution_error = False  # This is a valid SMT result, not an error
                elif "z3" in (output or "").lower() and ("error" in (output or "").lower() or "exception" in (output or "").lower()):
                    has_execution_error = True
                
                # Parse output and golden plan with timing using smart extraction
                pred_extract_start = time.time()
                
                # Z3 SPECIFIC: Use SMT-aware extraction for calendar tasks
                if task == "calendar":
                    # First try direct parsing from SMT output
                    predicted_output = self.parse_calendar_output(output if not has_execution_error else None)
                    
                    # If that fails, try smart extraction
                    if not predicted_output or ("day" not in predicted_output and "time_range" not in predicted_output):
                        smart_result = self.smart_extract_execution_result(output if not has_execution_error else None, task)
                        if isinstance(smart_result, dict) and "day" in smart_result and "start_time" in smart_result and "end_time" in smart_result:
                            # Convert smart extraction to our format
                            start_time = self.remove_leading_zeros(smart_result['start_time'])
                            end_time = self.remove_leading_zeros(smart_result['end_time'])
                            predicted_output = {
                                "day": smart_result["day"],
                                "time_range": f"{{{start_time}:{end_time}}}"
                            }
                elif task == "zebralogic":
                    predicted_output = config["parse_output"](output if not has_execution_error else None, golden_headers)
                else:
                    # Use smart extraction for execution results
                    predicted_output = config["parse_output"](output if not has_execution_error else None)
                    
                pred_extract_time = time.time() - pred_extract_start
                
                gold_extract_start = time.time()
                golden_output = config["parse_golden"](example_data["golden_plan"])
                gold_extract_time = time.time() - gold_extract_start
                
                # Task-specific plan detection
                if task == "calendar":
                    has_no_plan = (not has_execution_error and 
                                (predicted_output is None or 
                                "day" not in predicted_output or 
                                "time_range" not in predicted_output or
                                (isinstance(predicted_output, dict) and "no_solution" in predicted_output)))
                elif task == "zebralogic":
                    has_no_plan = (not has_execution_error and 
                                (predicted_output is None or 
                                not isinstance(predicted_output, list)))
                else:  # meeting or trip
                    has_no_plan = (not has_execution_error and 
                                (predicted_output is None or 
                                not predicted_output.get("itinerary")))
                
                # Evaluate constraints with timing
                constraint_eval_start = time.time()
                constraints_satisfied, violated = config["evaluate"](constraints, predicted_output)
                constraint_eval_time = time.time() - constraint_eval_start
                
                # Check if output matches golden solution
                is_exact_match = False
                try:
                    if predicted_output and golden_output:
                        # Convert to JSON string for comparison to handle object differences
                        pred_str = json.dumps(predicted_output, sort_keys=True)
                        gold_str = json.dumps(golden_output, sort_keys=True)
                        is_exact_match = pred_str == gold_str
                except:
                    is_exact_match = predicted_output == golden_output

                # Determine status
                if has_execution_error:
                    status = "Error"
                elif has_no_plan:
                    status = "No plan generated"
                elif constraints_satisfied:
                    status = "Correct plan"
                else:
                    status = "Wrong plan"
                
                # Prepare evaluation result with new structure including token info
                eval_result = {
                    "has_execution_error": has_execution_error,
                    "has_no_plan": has_no_plan,
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
                        "total_tokens": full_token_count,
                        "reasoning_tokens": reasoning_tokens
                    },
                    "reasoning_content": reasoning_content,
                    "generated_code": code  # Include the generated code for debugging
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
                
                # Only continue refinement if:
                # 1. There are code execution errors, OR
                # 2. The code runs but produces no valid plan
                if has_execution_error or has_no_plan:
                    if has_execution_error:
                        feedback = [
                            f"Previous code execution failed with error:\n{error if error else output}",
                            f"\nGenerated code that caused the error:\n```python\n{code}\n```",
                            "\nPlease fix the code to eliminate execution errors."
                        ]
                        if "z3" in (error or output or "").lower():
                            feedback.append("\nZ3-specific tips:")
                            feedback.append("- Ensure you import z3 correctly: `import z3`")
                            feedback.append("- Use `z3.Int('varname')` to create integer variables")
                            feedback.append("- Use `solver = z3.Solver()` and `solver.add(constraints)`")
                            feedback.append("- Check satisfiability with `solver.check() == z3.sat`")
                            
                    elif has_no_plan:
                        feedback = [
                            "The generated code ran successfully but produced no valid plan.",
                            f"\nCode output:\n{output}",
                            f"\nGenerated code:\n```python\n{code}\n```",
                            "\nPlease revise the code to generate a valid plan that meets the requirements."
                        ]
                    else:  # Constraints not satisfied
                        feedback = [
                            "The generated code produced a plan, but it violates constraints:",
                            config["format_feedback"](violated),
                            f"\nGenerated plan: {predicted_output}",
                            f"\nExpected plan: {golden_output}",
                            f"\nGenerated code:\n```python\n{code}\n```",
                            "\nPlease revise the code to satisfy all constraints."
                        ]
                    
                    current_prompt = "\n".join(feedback)
                else:
                    # Stop refinement since we have a valid solution
                    logging.info(f"Found valid solution for {task} example {example_id} in pass {pass_num}")
                    return

            logging.info(f"Reached maximum passes ({self.args.max_passes}) for {task} example {example_id} without finding valid solution")

    async def run(self):
        """Main execution method with parallel processing"""
        tasks_to_run = ["calendar", "meeting", "trip", "zebralogic"] if self.args.task == "all" else [self.args.task]
        
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
                    example_numbers = [int(num.strip()) for num in self.args.examples.split(",") if num.strip()]
                    if task == "calendar":
                        task_prefix = "calendar_scheduling"
                    elif task in ("meeting", "trip"):
                        task_prefix = f"{task}_planning"
                    elif task == "zebralogic":
                        task_prefix = "zebralogic"
                    examples = [(f"{task_prefix}_example_{num}", ex) 
                                for num in example_numbers 
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
        
        # Calculate and print token statistics
        self.calculate_token_statistics()

class EvaluationState:
    """Class to track evaluation state across runs"""
    def __init__(self, task_name):
        self.state_file = f"evaluation_state_{task_name}_{current_time}.json"
        self.data = {
            "calendar": {},
            "meeting": {},
            "trip": {},
            "zebralogic": {}
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
        for task in ["calendar", "meeting", "trip", "zebralogic"]:
            if not self.data[task]:
                continue
                
            total = len(self.data[task])
            completed = sum(1 for e in self.data[task].values() if e["completed"])
            exact_matches = sum(
                1 for e in self.data[task].values() 
                if any(p["is_exact_match"] for p in e["passes"])
            )
            
            # Count no-plan cases
            no_plan_cases = sum(
                1 for e in self.data[task].values()
                if any(p.get("has_no_plan", False) for p in e["passes"])
            )
            
            avg_passes = sum(
                len(e["passes"]) for e in self.data[task].values()
            ) / total
            
            print(f"\n{task.capitalize()} Task:")
            print(f"  Examples: {total}")
            print(f"  Completed: {completed} ({completed/total:.1%})")
            print(f"  Exact matches: {exact_matches} ({exact_matches/total:.1%})")
            print(f"  No-plan cases: {no_plan_cases} ({no_plan_cases/total:.1%})")
            print(f"  Average passes per example: {avg_passes:.1f}")

if __name__ == "__main__":
    program = SchedulingProgram()
    asyncio.run(program.run())