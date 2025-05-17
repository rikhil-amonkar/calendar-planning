import argparse
import asyncio
import json
import datetime
import re
import tiktoken
from kani import Kani
from kani.engines.huggingface import HuggingEngine
import os

# Load the calendar scheduling examples from the JSON file
with open('../../data/calendar_scheduling_100.json', 'r') as file:
    calendar_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

# Define state file location
STATE_FILE = "evaluation_state.json"

class EvaluationState:
    def __init__(self):
        self.correct_0shot = 0
        self.total_0shot = 0
        self.results_0shot = []
        self.processed_examples = set()
        self.start_time = datetime.datetime.now()
        self.paused_time = datetime.timedelta(0)
        self.first_run = True
        self.last_paused_time = None
        self.total_reasoning_tokens = 0

    def save(self):
        state_to_save = {
            "correct_0shot": self.correct_0shot,
            "total_0shot": self.total_0shot,
            "results_0shot": self.results_0shot,
            "processed_examples": list(self.processed_examples),
            "start_time": self.start_time.isoformat(),
            "paused_time": self.paused_time.total_seconds(),
            "first_run": self.first_run,
            "last_paused_time": self.last_paused_time.isoformat() if self.last_paused_time else None,
            "total_reasoning_tokens": self.total_reasoning_tokens
        }
        with open(STATE_FILE, 'w') as f:
            json.dump(state_to_save, f)

    def load(self):
        """Try loading the state from the file, if it exists. If not, create a new state."""
        if not os.path.exists(STATE_FILE):
            return False
        
        try:
            with open(STATE_FILE, 'r') as f:
                loaded = json.load(f)
                # Validate loaded state
                required_keys = ["correct_0shot", "total_0shot", "results_0shot", 
                               "processed_examples", "start_time", "paused_time"]
                if not all(k in loaded for k in required_keys):
                    return False
                
                self.correct_0shot = loaded["correct_0shot"]
                self.total_0shot = loaded["total_0shot"]
                self.results_0shot = loaded["results_0shot"]
                self.processed_examples = set(loaded["processed_examples"])
                self.paused_time = datetime.timedelta(seconds=loaded["paused_time"])
                self.start_time = datetime.datetime.fromisoformat(loaded["start_time"])
                self.last_paused_time = datetime.datetime.fromisoformat(loaded["last_paused_time"]) if loaded["last_paused_time"] else None
                self.first_run = loaded.get("first_run", False)
                self.total_reasoning_tokens = loaded.get("total_reasoning_tokens", 0)
            return True
        except (json.JSONDecodeError, KeyError, ValueError) as e:
            print(f"Error loading state: {e}")
            return False

    def calculate_total_elapsed_time(self):
        if self.last_paused_time:
            total_time = (datetime.datetime.now() - self.start_time) - self.paused_time
        else:
            total_time = (datetime.datetime.now() - self.start_time)
        return total_time

    def cleanup(self):
        """Remove the state file after successful completion"""
        if os.path.exists(STATE_FILE):
            os.remove(STATE_FILE)

def parse_golden_plan_time(golden_plan):
    match = re.search(r'(\w+), (\d{1,2}:\d{2}) - (\d{1,2}:\d{2})', golden_plan)
    if match:
        day_of_week, start_time, end_time = match.groups()
        return day_of_week, f"{{{start_time}:{end_time}}}"
    return "Invalid day format", "Invalid time format"

def extract_time_range(response):
    """Extracts HH:MM:HH:MM format from the model's raw response and removes leading zeros from single-digit hours."""
    if not response or not isinstance(response, str):
        return "Invalid response"
    
    match = re.search(r'(\d{1,2}:\d{2}):(\d{1,2}:\d{2})', response)
    if not match:
        return "Invalid response"
    
    start_time = match.group(1)
    end_time = match.group(2)
    
    def remove_leading_zero(time_str):
        parts = time_str.split(':')
        hour = parts[0].lstrip('0')
        return f"{hour}:{parts[1]}"
    
    start_time = remove_leading_zero(start_time)
    end_time = remove_leading_zero(end_time)
    
    return f"{{{start_time}:{end_time}}}"

def validate_time_range(time_range):
    """Validate that the time range matches the expected format."""
    return re.match(r'^\{\d{1,2}:\d{2}:\d{1,2}:\d{2}\}$', time_range) is not None

def extract_reasoning(response):
    """Attempt to extract the reasoning portion from the model's response."""
    # Try to find text before the JSON output
    json_match = re.search(r'\{.*\}', response)
    if json_match:
        reasoning = response[:json_match.start()].strip()
    else:
        reasoning = response.strip()
    return reasoning if reasoning else "No reasoning provided"

def count_tokens(text):
    """Count tokens using tiktoken."""
    encoding = tiktoken.encoding_for_model("gpt-4o")  # Use the encoding that works for your model
    tokens = encoding.encode(text)
    return len(tokens)

# Main execution
def main():
    # Initialize state management
    state = EvaluationState()
    state_loaded = state.load()

    # Create the Kani instance with just the HuggingEngine
    ai = Kani(HuggingEngine(model_id=args.model))

    # Open output files
    with open('DS-R1-8B-REASON_text_calendar_results.txt', 'a') as txt_file, \
         open('DS-R1-8B-REASON_text_calendar_results.json', 'w') as json_file:
        
        # Use loaded start time or create new one
        if state_loaded and not state.first_run:
            start_time = state.start_time
        else:
            start_time = datetime.datetime.now()
            state.start_time = start_time
            state.first_run = False

        for example_id, example in calendar_examples.items():
            if example_id in state.processed_examples:
                continue
            
            for prompt_type in ['prompt_0shot']:
                prompt = example[prompt_type]
                golden_plan = example['golden_plan']
                expected_day, expected_time = parse_golden_plan_time(golden_plan)

                # Keep the prompt exactly the same as before
                prompt += "\n\nPlease output the proposed time in the following JSON format:\n{\"time_range\": \"{HH:MM:HH:MM}\", \"day\": \"DayOfWeek\"}. For example, if the proposed time is 14:30 to 15:30, the output should be:\n{\"time_range\": \"{14:30:15:30}\", \"day\": \"Monday\"}"

                async def get_model_response():
                    full_response = ""
                    async for token in ai.chat_round_stream(prompt):
                        full_response += token
                        print(token, end="", flush=True)
                    print()
                    return full_response.strip()
                
                model_response = asyncio.run(get_model_response())
                print(f"Model response: {model_response}")

                # Extract reasoning and final answer separately
                model_reason = extract_reasoning(model_response)
                model_time = extract_time_range(model_response)
                
                if not validate_time_range(model_time):
                    model_time = "Invalid response"

                # Count reasoning tokens
                token_count = count_tokens(model_reason)
                state.total_reasoning_tokens += token_count
                print(f"Number of Tokens for {example_id}: {token_count}")

                # Clean curly braces for comparison
                expected_time_clean = expected_time.replace("{", "").replace("}", "")
                model_time_clean = model_time.replace("{", "").replace("}", "")

                # Extract day of week
                day_match = re.search(r'"day":"(.*?)"', model_response) or \
                           re.search(r'"day": "(.*?)"', model_response)
                day_of_week = day_match.group(1).strip() if day_match else "Invalid Day"

                # Prepare result entry
                result_entry = {
                    "final_program_time": {
                        "day": day_of_week,
                        "start_time": model_time_clean.split(":")[0] + ":" + model_time_clean.split(":")[1],
                        "end_time": model_time_clean.split(":")[2] + ":" + model_time_clean.split(":")[3]
                    },
                    "expected_time": {
                        "day": expected_day,
                        "start_time": expected_time_clean.split(":")[0] + ":" + expected_time_clean.split(":")[1],
                        "end_time": expected_time_clean.split(":")[2] + ":" + expected_time_clean.split(":")[3]
                    },
                    "reasoning_token_count": token_count,
                    "raw_model_response": model_response,
                    "raw_model_reasoning": model_reason,
                    "count": example_id
                }
                
                # Update state
                state.results_0shot.append(result_entry)
                state.total_0shot += 1
                if model_time_clean == expected_time_clean and day_of_week == expected_day:
                    state.correct_0shot += 1
                state.processed_examples.add(example_id)
                
                # Log results
                timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                log_line = f"{example_id}. [{timestamp}] | PROMPT TYPE: {prompt_type} | ANSWER: {{{model_time_clean}}}, {day_of_week} | EXPECTED: {{{expected_time_clean}}}, {expected_day} | REASONING TOKENS: {token_count}"
                print(log_line)
                txt_file.write(log_line + "\n")
                
                # Save state after each example
                state.save()

        # Final output
        json.dump({
            "0shot": state.results_0shot,
            "total_reasoning_tokens": state.total_reasoning_tokens
        }, json_file, indent=4)
        
        accuracy_0shot = (state.correct_0shot / state.total_0shot) * 100 if state.total_0shot > 0 else 0
        end_time = datetime.datetime.now()
        total_time = end_time - start_time
        average_tokens = state.total_reasoning_tokens / state.total_0shot if state.total_0shot > 0 else 0

        txt_file.write(f"\n0-shot prompts: Model guessed {state.correct_0shot} out of {state.total_0shot} correctly.\n")
        txt_file.write(f"Accuracy: {accuracy_0shot:.2f}%\n")
        txt_file.write(f"Total time taken: {total_time}\n")
        txt_file.write(f"Total reasoning tokens: {state.total_reasoning_tokens}\n")
        txt_file.write(f"Average reasoning tokens per example: {average_tokens:.2f}\n")

        # Clean up state file if we processed all examples
        if len(state.processed_examples) == len(calendar_examples):
            state.cleanup()

    print("Processing complete. Results saved.")

if __name__ == "__main__":
    main()

