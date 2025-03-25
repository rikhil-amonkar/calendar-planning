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

# Define the structured JSON schema for the trip plan output
JSON_SCHEMA = {
    "type": "object",
    "properties": {
        "itinerary": {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "day_range": {"type": "string", "pattern": "^Day \\d+-\\d+$"},
                    "place": {"type": "string"}
                },
                "required": ["day_range", "place"]
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

# Load the model selected by the user
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

model = HuggingEngine(model_id=args.model)
engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)
ai = Kani(engine)

def parse_golden_plan(golden_plan):
    """Parse the golden plan into structured itinerary format matching our JSON schema."""
    itinerary = []
    current_day = 1
    
    # Split the plan into lines and process each line
    for line in golden_plan.split('\n'):
        line = line.strip()
        if not line or not line.startswith('**Day'):
            continue
            
        # Extract day range and place
        day_match = re.search(r'Day (\d+)(?:-(\d+))?', line)
        place_match = re.search(r': (.*?)(?: for \d+ days|$)', line)
        
        if not day_match or not place_match:
            continue
            
        start_day = int(day_match.group(1))
        end_day = int(day_match.group(2)) if day_match.group(2) else start_day
        place = place_match.group(1).strip()
        
        # Remove "Arriving in" prefix if present
        if place.startswith("Arriving in "):
            place = place[12:]
        
        # Remove "Fly from X to Y" if present and take destination
        if "Fly from" in place:
            place = place.split(" to ")[-1]
        
        # Remove "Visit " prefix if present
        if place.startswith("Visit "):
            place = place[6:]
        
        # Add to itinerary
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": place
        })
        
        current_day = end_day + 1

        print(itinerary)
    
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

# Initialize counters
correct_0shot = 0
correct_5shot = 0
total_0shot = 0
total_5shot = 0

# Initialize results lists
results_0shot = []
results_5shot = []

# Output files
with open('structured_trip_results.txt', 'w') as txt_file, open('structured_trip_results.json', 'w') as json_file:
    start_time = datetime.datetime.now()
    
    for example_id, example in trip_examples.items():
        for prompt_type in ['prompt_0shot', 'prompt_5shot']:
            prompt = example[prompt_type]
            golden_plan = example['golden_plan']

            # Parse golden plan into structured format
            golden_itinerary = parse_golden_plan(golden_plan)

            # Modify prompt to request structured JSON output
            structured_prompt = (
                f"{prompt}\n\nPlease provide your trip plan in the following exact JSON format:\n"
                "{\n"
                '  "itinerary": [\n'
                '    {"day_range": "Day X-Y", "place": "City Name"},\n'
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
            
            model_response = asyncio.run(get_model_response())

            try:
                model_data = json.loads(model_response)
                model_itinerary = model_data.get("itinerary", [])
            except json.JSONDecodeError:
                model_itinerary = []

            # Compare with golden itinerary
            is_correct = compare_itineraries(model_itinerary, golden_itinerary)

            # Update counters
            if prompt_type == 'prompt_0shot':
                total_0shot += 1
                if is_correct:
                    correct_0shot += 1
            else:
                total_5shot += 1
                if is_correct:
                    correct_5shot += 1

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
                results_0shot.append(result_entry)
            else:
                results_5shot.append(result_entry)

            # Log output
            timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            output_line = f"{example_id}. [{timestamp}] | {prompt_type} | Correct: {is_correct}"
            print(output_line)
            txt_file.write(f"{output_line}\n")
            txt_file.write(f"Model: {json.dumps(model_itinerary, indent=2)}\n")
            txt_file.write(f"Golden: {json.dumps(golden_itinerary, indent=2)}\n\n")

    # Save JSON results
    json.dump({
        "0shot": results_0shot,
        "5shot": results_5shot,
        "accuracy": {
            "0shot": correct_0shot / total_0shot if total_0shot > 0 else 0,
            "5shot": correct_5shot / total_5shot if total_5shot > 0 else 0,
            "total": (correct_0shot + correct_5shot) / (total_0shot + total_5shot) if (total_0shot + total_5shot) > 0 else 0
        }
    }, json_file, indent=4)

    # Final accuracy report
    end_time = datetime.datetime.now()
    total_time = end_time - start_time
    txt_file.write("\n=== Final Results ===\n")
    txt_file.write(f"0-shot accuracy: {correct_0shot}/{total_0shot} ({correct_0shot/total_0shot:.2%})\n")
    txt_file.write(f"5-shot accuracy: {correct_5shot}/{total_5shot} ({correct_5shot/total_5shot:.2%})\n")
    txt_file.write(f"Total accuracy: {correct_0shot + correct_5shot}/{total_0shot + total_5shot} ({(correct_0shot + correct_5shot)/(total_0shot + total_5shot):.2%})\n")
    txt_file.write(f"Total time: {total_time}\n")

print("Processing complete. Results saved to structured_trip_results.txt and structured_trip_results.json.")