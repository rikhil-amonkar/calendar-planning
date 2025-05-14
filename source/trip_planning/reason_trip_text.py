import argparse
import asyncio
import json
import datetime
import re
import tiktoken
from kani import Kani
from kani.engines.huggingface import HuggingEngine
import os

# Load the trip planning examples from the JSON file
with open('../../data/trip_planning_100.json', 'r') as file:
    trip_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

# State management
STATE_FILE = "trip_planning_state.json"

class EvaluationState:
    def __init__(self):
        self.correct_0shot = 0
        self.total_0shot = 0
        self.results_0shot = []
        self.processed_examples = set()
        self.start_time = datetime.datetime.now()
        self.previous_time = datetime.timedelta(0)
        self.first_run = True
        self.total_reasoning_tokens = 0

    def save(self):
        state_to_save = {
            "correct_0shot": self.correct_0shot,
            "total_0shot": self.total_0shot,
            "results_0shot": self.results_0shot,
            "processed_examples": list(self.processed_examples),
            "start_time": self.start_time.isoformat(),
            "previous_time": self.previous_time.total_seconds(),
            "first_run": self.first_run,
            "total_reasoning_tokens": self.total_reasoning_tokens
        }
        with open(STATE_FILE, 'w') as f:
            json.dump(state_to_save, f)

    def load(self):
        try:
            with open(STATE_FILE, 'r') as f:
                loaded = json.load(f)
                self.correct_0shot = loaded["correct_0shot"]
                self.total_0shot = loaded["total_0shot"]
                self.results_0shot = loaded["results_0shot"]
                self.processed_examples = set(loaded["processed_examples"])
                self.previous_time = datetime.timedelta(seconds=loaded["previous_time"])
                self.start_time = datetime.datetime.fromisoformat(loaded["start_time"])
                self.first_run = loaded.get("first_run", False)
                self.total_reasoning_tokens = loaded.get("total_reasoning_tokens", 0)
            return True
        except (FileNotFoundError, json.JSONDecodeError, KeyError):
            return False

def parse_golden_plan(golden_plan):
    """Parse the golden plan into structured itinerary format (only day ranges and places)."""
    itinerary = []
    
    # Split the plan into lines and process each line
    for line in golden_plan.split('\n'):
        line = line.strip()
        if not line or not line.startswith('**Day'):
            continue
            
        # Extract day range
        day_match = re.search(r'Day (\d+)(?:-(\d+))?', line)
        if not day_match:
            continue
            
        start_day = int(day_match.group(1))
        end_day = int(day_match.group(2)) if day_match.group(2) else start_day
        day_range = f"Day {start_day}-{end_day}"
        
        # Skip flying days (we're only interested in places)
        if "Fly from" in line:
            continue
            
        # Handle regular days
        if "Arriving in" in line:
            place = re.search(r'Arriving in ([^\s,.]+)', line).group(1)
        elif "Visit" in line:
            place = re.search(r'Visit ([^\s,.]+)', line).group(1)
        else:
            continue  # skip if we couldn't determine the place
            
        # Add to itinerary
        itinerary.append({
            "day_range": day_range,
            "place": place
        })
    
    return itinerary

def compare_itineraries(model_itinerary, golden_itinerary):
    """Compare two itineraries and return True if they match exactly."""
    if len(model_itinerary) != len(golden_itinerary):
        return False
    
    for model_item, golden_item in zip(model_itinerary, golden_itinerary):
        if (model_item["day_range"] != golden_item["day_range"] or 
            model_item["place"] != golden_item["place"]):
            return False
    
    return True

def format_itinerary_compact(itinerary):
    """Convert itinerary to compact string representation for display."""
    return ", ".join([f"{item['day_range']}: {item['place']}" for item in itinerary])

def extract_reasoning(response):
    """Attempt to extract the reasoning portion from the model's response."""
    # Try to find text before the JSON output
    json_match = re.search(r'\{.*\}', response, re.DOTALL)
    if json_match:
        reasoning = response[:json_match.start()].strip()
    else:
        reasoning = response.strip()
    return reasoning if reasoning else "No reasoning provided"

def count_tokens(text):
    """Count tokens using tiktoken."""
    try:
        encoding = tiktoken.encoding_for_model("gpt-4")
    except ValueError:
        encoding = tiktoken.get_encoding("cl100k_base")
    tokens = encoding.encode(text)
    return len(tokens)

def extract_json_response(response):
    """Extract JSON from response, handling various formats."""
    try:
        # First try to parse the entire response as JSON
        data = json.loads(response)
        
        # Check if it's wrapped in a SOLUTION object
        if isinstance(data, dict) and "SOLUTION" in data and "itinerary" in data["SOLUTION"]:
            return data["SOLUTION"]["itinerary"]
        elif isinstance(data, dict) and "itinerary" in data:
            return data["itinerary"]
        return []
    except json.JSONDecodeError:
        # If full response isn't JSON, try to find JSON portion
        json_match = re.search(r'\{.*\}', response, re.DOTALL)
        if json_match:
            try:
                data = json.loads(json_match.group(0))
                if isinstance(data, dict) and "SOLUTION" in data and "itinerary" in data["SOLUTION"]:
                    return data["SOLUTION"]["itinerary"]
                elif isinstance(data, dict) and "itinerary" in data:
                    return data["itinerary"]
                return []
            except json.JSONDecodeError:
                return []
    return []

async def main():
    # Initialize the Kani AI with the selected model
    ai = Kani(HuggingEngine(model_id=args.model))

    # Initialize state
    state = EvaluationState()
    state_loaded = state.load()

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'
    json_mode = 'a' if state_loaded and not state.first_run else 'w'

    with open('DS-R1-8B-REASON_text_trip_results.txt', txt_mode) as txt_file, \
         open('DS-R1-8B-REASON_text_trip_results.json', json_mode) as json_file:
        
        # Write header if this is a fresh run
        if not state_loaded or state.first_run:
            json_file.write("")
            state.first_run = False

        for example_id, example in trip_examples.items():
            # Skip already processed examples
            if example_id in state.processed_examples:
                continue
                
            for prompt_type in ['prompt_0shot']:
                prompt = example[prompt_type]
                golden_plan = example['golden_plan']

                # Parse golden plan into structured format (only day ranges and places)
                golden_itinerary = parse_golden_plan(golden_plan)

                # Simplified prompt focusing only on day ranges and places
                structured_prompt = (
                    "You are an AI trip planner and your task is to plan a trip itinerary. "
                    "Focus only on day ranges and places - do not include any transportation details. "
                    f"{prompt}\n\n"
                    "Provide your response in the following exact JSON format:\n"
                    "{\n"
                    '  "itinerary": [\n'
                    '    {"day_range": "Day X-Y", "place": "City Name"},\n'
                    '    {"day_range": "Day Y-Z", "place": "City Name"}\n'
                    "  ]\n"
                    "}\n"
                    "Include only the JSON with no additional text or explanation."
                )

                # Run the model
                async def get_model_response():
                    full_response = ""
                    async for token in ai.chat_round_stream(structured_prompt):
                        full_response += token
                        print(token, end="", flush=True)
                    print()
                    return full_response.strip()
                
                model_response = await get_model_response()
                print(f"Model response: {model_response}")

                # Extract reasoning and count tokens
                model_reason = extract_reasoning(model_response)
                try:
                    token_count = count_tokens(model_reason)
                    state.total_reasoning_tokens += token_count
                    print(f"Number of Tokens for {example_id}: {token_count}")
                except Exception as e:
                    print(f"Error counting tokens: {e}")
                    token_count = 0

                # Extract JSON itinerary from response
                model_itinerary = extract_json_response(model_response)
                
                # Filter out any flying entries (just in case)
                model_itinerary = [item for item in model_itinerary 
                                 if isinstance(item, dict) and "day_range" in item and "place" in item]

                # Compare with golden itinerary
                is_correct = compare_itineraries(model_itinerary, golden_itinerary)

                # Update state
                state.total_0shot += 1
                if is_correct:
                    state.correct_0shot += 1

                # Prepare result entry
                result_entry = {
                    "final_program_time": {"itinerary": model_itinerary},
                    "expected_time": {"itinerary": golden_itinerary},
                    "count": example_id,
                    "is_correct": is_correct,
                    "reasoning": model_reason,
                    "reasoning_tokens": token_count,
                    "raw_model_response": model_response
                }

                # Store results
                state.results_0shot.append(result_entry)

                # Format for display
                model_display = format_itinerary_compact(model_itinerary)
                golden_display = format_itinerary_compact(golden_itinerary)
                
                # Log output
                timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                output_line = (
                    f"{example_id}. [{timestamp}] | Correct: {is_correct} | "
                    f"ANSWER: {model_display} | EXPECTED: {golden_display} | "
                    f"REASONING TOKENS: {token_count}"
                )
                print(output_line)
                txt_file.write(f"{output_line}\n")

                # Save state after each example
                state.processed_examples.add(example_id)
                state.save()

        # Final results handling
        current_time = datetime.datetime.now()
        total_runtime = state.previous_time + (current_time - state.start_time)
        
        # Calculate accuracy and average tokens
        accuracy_0shot = state.correct_0shot / state.total_0shot if state.total_0shot > 0 else 0
        average_tokens = state.total_reasoning_tokens / state.total_0shot if state.total_0shot > 0 else 0
        
        # Save final JSON results
        final_results = {
            "0shot": state.results_0shot,
            "metadata": {
                "accuracy": accuracy_0shot,
                "correct_count": state.correct_0shot,
                "total_count": state.total_0shot,
                "total_reasoning_tokens": state.total_reasoning_tokens,
                "average_reasoning_tokens": average_tokens,
                "start_time": state.start_time.isoformat(),
                "end_time": current_time.isoformat(),
                "total_runtime_seconds": total_runtime.total_seconds()
            }
        }
        json.dump(final_results, json_file, indent=4)

        # Final accuracy report
        txt_file.write("\n=== Final Results ===\n")
        txt_file.write(f"0-shot accuracy: {state.correct_0shot}/{state.total_0shot} ({accuracy_0shot:.2%})\n")
        txt_file.write(f"Total reasoning tokens: {state.total_reasoning_tokens}\n")
        txt_file.write(f"Average reasoning tokens: {average_tokens:.2f}\n")
        txt_file.write(f"Total time: {total_runtime}\n")

    print("Processing complete. Results saved.")

if __name__ == "__main__":
    asyncio.run(main())

