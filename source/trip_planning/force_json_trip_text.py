# #**********WORKING CODE, FORCE JSON, TEXT OUTPUTS, TRIP PLANNING, KANI, CHECKPOINT************

import argparse
import asyncio
import json
import datetime
import outlines
import transformers
import re
from kani import Kani
from kani.engines.huggingface import HuggingEngine
from kani.engines import WrapperEngine
import os

# Define the structured JSON schema for the trip plan output
JSON_SCHEMA = {
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

# Load the trip planning examples from the JSON file
with open('100_trip_planning_examples.json', 'r') as file:
    trip_examples = json.load(file)

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

# State management
STATE_FILE = "trip_planning_state.json"

class JSONGuidanceHFWrapper(WrapperEngine):
    def __init__(self, engine: HuggingEngine, *args, json_schema, **kwargs):
        super().__init__(engine, *args, **kwargs)
        self.engine: HuggingEngine  # type hint for IDEs
        self.json_schema = json_schema
        self.outlines_tokenizer = outlines.models.TransformerTokenizer(self.engine.tokenizer)

    def _create_logits_processor(self):
        json_logits_processor = outlines.processors.JSONLogitsProcessor(self.json_schema, self.outlines_tokenizer)
        return transformers.LogitsProcessorList([json_logits_processor])

    async def predict(self, *args, **kwargs):
        if "logits_processor" not in kwargs:
            kwargs["logits_processor"] = self._create_logits_processor()
        return await super().predict(*args, **kwargs)

    async def stream(self, *args, **kwargs):
        if "logits_processor" not in kwargs:
            kwargs["logits_processor"] = self._create_logits_processor()
        async for elem in super().stream(*args, **kwargs):
            yield elem

class EvaluationState:
    def __init__(self):
        self.correct_0shot = 0
        self.correct_5shot = 0
        self.total_0shot = 0
        self.total_5shot = 0
        self.results_0shot = []
        self.results_5shot = []
        self.processed_examples = set()
        self.start_time = datetime.datetime.now()
        self.previous_time = datetime.timedelta(0)
        self.first_run = True

    def save(self):
        state_to_save = {
            "correct_0shot": self.correct_0shot,
            "correct_5shot": self.correct_5shot,
            "total_0shot": self.total_0shot,
            "total_5shot": self.total_5shot,
            "results_0shot": self.results_0shot,
            "results_5shot": self.results_5shot,
            "processed_examples": list(self.processed_examples),
            "start_time": self.start_time.isoformat(),
            "previous_time": self.previous_time.total_seconds(),
            "first_run": self.first_run
        }
        with open(STATE_FILE, 'w') as f:
            json.dump(state_to_save, f)

    def load(self):
        try:
            with open(STATE_FILE, 'r') as f:
                loaded = json.load(f)
                self.correct_0shot = loaded["correct_0shot"]
                self.correct_5shot = loaded["correct_5shot"]
                self.total_0shot = loaded["total_0shot"]
                self.total_5shot = loaded["total_5shot"]
                self.results_0shot = loaded["results_0shot"]
                self.results_5shot = loaded["results_5shot"]
                self.processed_examples = set(loaded["processed_examples"])
                self.previous_time = datetime.timedelta(seconds=loaded["previous_time"])
                self.start_time = datetime.datetime.fromisoformat(loaded["start_time"])
                self.first_run = loaded.get("first_run", False)
            return True
        except (FileNotFoundError, json.JSONDecodeError, KeyError):
            return False

def parse_golden_plan(golden_plan):
    """Parse the golden plan into structured itinerary format matching our JSON schema."""
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
        
        # Handle flying days
        if "Fly from" in line:
            fly_match = re.search(r'Fly from ([^\s,.]+) to ([^\s,.]+)', line)
            if fly_match:
                itinerary.append({
                    "flying": day_range,
                    "from": fly_match.group(1),
                    "to": fly_match.group(2)
                })
            continue
        # Handle regular days
        elif "Arriving in" in line:
            place = re.search(r'Arriving in ([^\s,.]+)', line).group(1)
        elif "Visit" in line:
            place = re.search(r'Visit ([^\s,.]+)', line).group(1)
        else:
            continue  # skip if we couldn't determine the type
            
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
        # Check if both items are the same type
        if ("day_range" in model_item) != ("day_range" in golden_item):
            return False
        if ("flying" in model_item) != ("flying" in golden_item):
            return False
        
        # Compare based on type
        if "day_range" in model_item:
            if (model_item["day_range"] != golden_item["day_range"] or 
                model_item["place"] != golden_item["place"]):
                return False
        elif "flying" in model_item:
            if (model_item["flying"] != golden_item["flying"] or 
                model_item["from"] != golden_item["from"] or 
                model_item["to"] != golden_item["to"]):
                return False
    
    return True

def format_itinerary_compact(itinerary):
    """Convert itinerary to compact string representation for display."""
    parts = []
    for item in itinerary:
        if "day_range" in item:
            parts.append(f"{item['day_range']}: {item['place']}")
        elif "flying" in item:
            parts.append(f"{item['flying']}: {item['from']}→{item['to']}")
    return ", ".join(parts)

async def main():
    # Initialize the Kani AI with the selected model
    model = HuggingEngine(model_id=args.model)
    engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)
    ai = Kani(engine)

    # Initialize state
    state = EvaluationState()
    state_loaded = state.load()

    # Determine file open mode
    txt_mode = 'a' if state_loaded and not state.first_run else 'w'
    json_mode = 'a' if state_loaded and not state.first_run else 'w'

    with open('DS-R1-DL-70B_forceJSON_text_trip_results.txt', txt_mode) as txt_file, \
         open('DS-R1-DL-70B_forceJSON_text_trip_results.json', json_mode) as json_file:
        
        # Write header if this is a fresh run
        if not state_loaded or state.first_run:
            txt_file.write("=== New Run Started ===\n")
            json_file.write("")  # Will be properly initialized later
            state.first_run = False

        for example_id, example in trip_examples.items():
            # Skip already processed examples
            if example_id in state.processed_examples:
                continue
                
            for prompt_type in ['prompt_0shot', 'prompt_5shot']:
                prompt = example[prompt_type]
                golden_plan = example['golden_plan']

                # Parse golden plan into structured format
                golden_itinerary = parse_golden_plan(golden_plan)

                # Modify prompt to request structured JSON output
                structured_prompt = (
                    "You are a AI trip planner and your task is to plan a trip for a user. "
                    "Days that involve flying happen on the same day. Include them in the plan with the flying details. "
                    "Ensure clear, structured, and diverse responses. avoiding unnecessary repetition. "
                    f"{prompt}\n\nPlease provide your trip plan in the following exact JSON format:\n"
                    "{\n"
                    '  "itinerary": [\n'
                    '    {"day_range": "Day X-Y", "place": "City Name"},\n'
                    '    {"flying": "Day Y-Y", "from": "City Name", "to": "City Name"},\n'
                    '    {"day_range": "Day Y-Z", "place": "City Name"}\n'
                    "  ]\n"
                    "}"
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

                try:
                    model_data = json.loads(model_response)
                    model_itinerary = model_data.get("itinerary", [])
                except json.JSONDecodeError:
                    model_itinerary = []

                # Compare with golden itinerary
                is_correct = compare_itineraries(model_itinerary, golden_itinerary)

                # Update state
                if prompt_type == 'prompt_0shot':
                    state.total_0shot += 1
                    if is_correct:
                        state.correct_0shot += 1
                else:
                    state.total_5shot += 1
                    if is_correct:
                        state.correct_5shot += 1

                # Prepare result entry
                result_entry = {
                    "example_id": example_id,
                    "prompt_type": prompt_type,
                    "model_response": model_response,
                    "model_itinerary": model_itinerary,
                    "golden_itinerary": golden_itinerary,
                    "is_correct": is_correct
                }

                # Store results
                if prompt_type == 'prompt_0shot':
                    state.results_0shot.append(result_entry)
                else:
                    state.results_5shot.append(result_entry)

                # Format for display
                model_display = format_itinerary_compact(model_itinerary)
                golden_display = format_itinerary_compact(golden_itinerary)
                
                # Log output
                timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                output_line = (
                    f"{example_id}. [{timestamp}] | {prompt_type} | Correct: {is_correct} | ANSWER: {model_display} | EXPECTED: {golden_display}"
                )
                print(output_line)
                txt_file.write(f"{output_line}\n")

                # Save state after each prompt type
                state.processed_examples.add(example_id)
                state.save()

        # Final results handling
        current_time = datetime.datetime.now()
        total_runtime = state.previous_time + (current_time - state.start_time)
        
        # Save final JSON results
        json.dump({
            "0shot": state.results_0shot,
            "5shot": state.results_5shot,
            "accuracy": {
                "0shot": state.correct_0shot / state.total_0shot if state.total_0shot > 0 else 0,
                "5shot": state.correct_5shot / state.total_5shot if state.total_5shot > 0 else 0,
                "total": (state.correct_0shot + state.correct_5shot) / (state.total_0shot + state.total_5shot) if (state.total_0shot + state.total_5shot) > 0 else 0
            }
        }, json_file, indent=4)

        # Final accuracy report
        txt_file.write("\n=== Final Results ===\n")
        txt_file.write(f"0-shot accuracy: {state.correct_0shot}/{state.total_0shot} ({state.correct_0shot/state.total_0shot:.2%})\n")
        txt_file.write(f"5-shot accuracy: {state.correct_5shot}/{state.total_5shot} ({state.correct_5shot/state.total_5shot:.2%})\n")
        txt_file.write(f"Total accuracy: {state.correct_0shot + state.correct_5shot}/{state.total_0shot + state.total_5shot} ({(state.correct_0shot + state.correct_5shot)/(state.total_0shot + state.total_5shot):.2%})\n")
        txt_file.write(f"Total time: {total_runtime}\n")

    print("Processing complete. Results saved.")

if __name__ == "__main__":
    asyncio.run(main())


# #**********WORKING CODE, FORCE JSON, TEXT OUTPUTS, TRIP PLANNING, KANI************

# import argparse
# import asyncio
# import json
# import datetime
# import outlines
# import transformers
# import re
# from kani import Kani
# from kani.engines.huggingface import HuggingEngine
# from kani.engines import WrapperEngine

# # Define the structured JSON schema for the trip plan output
# JSON_SCHEMA = {
#     "type": "object",
#     "properties": {
#         "itinerary": {
#             "type": "array",
#             "items": {
#                 "anyOf": [
#                     {
#                         "type": "object",
#                         "properties": {
#                             "day_range": {"type": "string", "pattern": "^Day \\d+-\\d+$"},
#                             "place": {"type": "string"}
#                         },
#                         "required": ["day_range", "place"]
#                     },
#                     {
#                         "type": "object",
#                         "properties": {
#                             "flying": {"type": "string", "pattern": "^Day \\d+-\\d+$"},
#                             "from": {"type": "string"},
#                             "to": {"type": "string"}
#                         },
#                         "required": ["flying", "from", "to"]
#                     }
#                 ]
#             }
#         }
#     },
#     "required": ["itinerary"]
# }

# # Load the trip planning examples from the JSON file
# with open('100_trip_planning_examples.json', 'r') as file:
#     trip_examples = json.load(file)

# # Argument parser to select the model
# parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
# parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
# args = parser.parse_args()

# # Load the model selected by the user
# class JSONGuidanceHFWrapper(WrapperEngine):
#     def __init__(self, engine: HuggingEngine, *args, json_schema, **kwargs):
#         super().__init__(engine, *args, **kwargs)
#         self.engine: HuggingEngine  # type hint for IDEs
#         self.json_schema = json_schema
#         self.outlines_tokenizer = outlines.models.TransformerTokenizer(self.engine.tokenizer)

#     def _create_logits_processor(self):
#         json_logits_processor = outlines.processors.JSONLogitsProcessor(self.json_schema, self.outlines_tokenizer)
#         return transformers.LogitsProcessorList([json_logits_processor])

#     async def predict(self, *args, **kwargs):
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         return await super().predict(*args, **kwargs)

#     async def stream(self, *args, **kwargs):
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         async for elem in super().stream(*args, **kwargs):
#             yield elem

# # Initialize the Kani AI with the selected model
# model = HuggingEngine(
#     model_id=args.model,
#     temperature=0.4,
#     top_k=50,
#     top_p=0.9,
#     repetition_penalty=1.2,
# )

# engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)
# ai = Kani(engine)

# def parse_golden_plan(golden_plan):
#     """Parse the golden plan into structured itinerary format matching our JSON schema."""
#     itinerary = []
    
#     # Split the plan into lines and process each line
#     for line in golden_plan.split('\n'):
#         line = line.strip()
#         if not line or not line.startswith('**Day'):
#             continue
            
#         # Extract day range
#         day_match = re.search(r'Day (\d+)(?:-(\d+))?', line)
#         if not day_match:
#             continue
            
#         start_day = int(day_match.group(1))
#         end_day = int(day_match.group(2)) if day_match.group(2) else start_day
#         day_range = f"Day {start_day}-{end_day}"
        
#         # Handle flying days
#         if "Fly from" in line:
#             fly_match = re.search(r'Fly from ([^\s,.]+) to ([^\s,.]+)', line)
#             if fly_match:
#                 itinerary.append({
#                     "flying": day_range,
#                     "from": fly_match.group(1),
#                     "to": fly_match.group(2)
#                 })
#             continue
#         # Handle regular days
#         elif "Arriving in" in line:
#             place = re.search(r'Arriving in ([^\s,.]+)', line).group(1)
#         elif "Visit" in line:
#             place = re.search(r'Visit ([^\s,.]+)', line).group(1)
#         else:
#             continue  # skip if we couldn't determine the type
            
#         # Add to itinerary
#         itinerary.append({
#             "day_range": day_range,
#             "place": place
#         })
    
#     return itinerary

# def compare_itineraries(model_itinerary, golden_itinerary):
#     """Compare two itineraries and return True if they match exactly."""
#     if len(model_itinerary) != len(golden_itinerary):
#         return False
    
#     for model_item, golden_item in zip(model_itinerary, golden_itinerary):
#         # Check if both items are the same type
#         if ("day_range" in model_item) != ("day_range" in golden_item):
#             return False
#         if ("flying" in model_item) != ("flying" in golden_item):
#             return False
        
#         # Compare based on type
#         if "day_range" in model_item:
#             if (model_item["day_range"] != golden_item["day_range"] or 
#                 model_item["place"] != golden_item["place"]):
#                 return False
#         elif "flying" in model_item:
#             if (model_item["flying"] != golden_item["flying"] or 
#                 model_item["from"] != golden_item["from"] or 
#                 model_item["to"] != golden_item["to"]):
#                 return False
    
#     return True

# def format_itinerary_compact(itinerary):
#     """Convert itinerary to compact string representation for display."""
#     parts = []
#     for item in itinerary:
#         if "day_range" in item:
#             parts.append(f"{item['day_range']}: {item['place']}")
#         elif "flying" in item:
#             parts.append(f"{item['flying']}: {item['from']}→{item['to']}")
#     return ", ".join(parts)

# # Initialize counters
# correct_0shot = 0
# correct_5shot = 0
# total_0shot = 0
# total_5shot = 0

# # Initialize results lists
# results_0shot = []
# results_5shot = []

# # Output files
# with open('DS-R1-DL-8B_forceJSON_text_trip_results.txt', 'w') as txt_file, open('DS-R1-DL-8B_forceJSON_text_trip_results.json', 'w') as json_file:
#     start_time = datetime.datetime.now()
    
#     for example_id, example in trip_examples.items():
#         for prompt_type in ['prompt_0shot', 'prompt_5shot']:
#             prompt = example[prompt_type]
#             golden_plan = example['golden_plan']

#             # Parse golden plan into structured format
#             golden_itinerary = parse_golden_plan(golden_plan)

#             # Modify prompt to request structured JSON output
#             structured_prompt = (
#                 "You are a AI trip planner and your task is to plan a trip for a user. "
#                 "Days that involve flying happen on the same day. Include them in the plan with the flying details. "
#                 "Ensure clear, structured, and diverse responses. avoiding unnecessary repetition. "
#                 f"{prompt}\n\nPlease provide your trip plan in the following exact JSON format:\n"
#                 "{\n"
#                 '  "itinerary": [\n'
#                 '    {"day_range": "Day X-Y", "place": "City Name"},\n'
#                 '    {"flying": "Day Y-Y", "from": "City Name", "to": "City Name"},\n'
#                 '    {"day_range": "Day Y-Z", "place": "City Name"}\n'
#                 "  ]\n"
#                 "}"
#             )

#             # Run the model
#             async def get_model_response():
#                 full_response = ""
#                 async for token in ai.chat_round_stream(structured_prompt):
#                     full_response += token
#                     print(token, end="", flush=True)
#                 print()
#                 return full_response.strip()
            
#             model_response = asyncio.run(get_model_response())

#             try:
#                 model_data = json.loads(model_response)
#                 model_itinerary = model_data.get("itinerary", [])
#             except json.JSONDecodeError:
#                 model_itinerary = []

#             # Compare with golden itinerary
#             is_correct = compare_itineraries(model_itinerary, golden_itinerary)

#             # Update counters
#             if prompt_type == 'prompt_0shot':
#                 total_0shot += 1
#                 if is_correct:
#                     correct_0shot += 1
#             else:
#                 total_5shot += 1
#                 if is_correct:
#                     correct_5shot += 1

#             # Prepare result entry
#             result_entry = {
#                 "example_id": example_id,
#                 "prompt_type": prompt_type,
#                 "model_response": model_response,
#                 "model_itinerary": model_itinerary,
#                 "golden_itinerary": golden_itinerary,
#                 "is_correct": is_correct
#             }

#             # Store results
#             if prompt_type == 'prompt_0shot':
#                 results_0shot.append(result_entry)
#             else:
#                 results_5shot.append(result_entry)

#             # Format for display
#             model_display = format_itinerary_compact(model_itinerary)
#             golden_display = format_itinerary_compact(golden_itinerary)
            
#             # Log output
#             timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
#             output_line = (
#                 f"{example_id}. [{timestamp}] | {prompt_type} | Correct: {is_correct} | ANSWER: {model_display} | EXPECTED: {golden_display}"
#             )
#             print(output_line)
#             txt_file.write(f"{output_line}\n")

#     # Save JSON results
#     json.dump({
#         "0shot": results_0shot,
#         "5shot": results_5shot,
#         "accuracy": {
#             "0shot": correct_0shot / total_0shot if total_0shot > 0 else 0,
#             "5shot": correct_5shot / total_5shot if total_5shot > 0 else 0,
#             "total": (correct_0shot + correct_5shot) / (total_0shot + total_5shot) if (total_0shot + total_5shot) > 0 else 0
#         }
#     }, json_file, indent=4)

#     # Final accuracy report
#     end_time = datetime.datetime.now()
#     total_time = end_time - start_time
#     txt_file.write("\n=== Final Results ===\n")
#     txt_file.write(f"0-shot accuracy: {correct_0shot}/{total_0shot} ({correct_0shot/total_0shot:.2%})\n")
#     txt_file.write(f"5-shot accuracy: {correct_5shot}/{total_5shot} ({correct_5shot/total_5shot:.2%})\n")
#     txt_file.write(f"Total accuracy: {correct_0shot + correct_5shot}/{total_0shot + total_5shot} ({(correct_0shot + correct_5shot)/(total_0shot + total_5shot):.2%})\n")
#     txt_file.write(f"Total time: {total_time}\n")

# print("Processing complete. Results saved to structured_trip_results.txt and structured_trip_results.json.")

