import os
import json
from kani import Kani
from kani.engines.huggingface import HuggingEngine
import asyncio
from argparse import ArgumentParser
from datetime import datetime
import torch  # For clearing GPU cache
import outlines
import transformers
import re

# Argument parser for model selection
parser = ArgumentParser()
parser.add_argument("--model", dest="model", help="Model name to use")
args = parser.parse_args()


# Load the prompts from the JSON file
with open("100_prompt_scheduling.json", "r") as file:
   prompts_data = json.load(file)

JSON_SCHEMA = {
    "type": "object",
    "properties": {
        "time_range": {
            "type": "string",
            "pattern": "^\\{\\d{2}:\\d{2}:\\d{2}:\\d{2}\\}$"
        }
    },
    "required": ["time_range"],
}

# Define prefix and suffix messages
prefix_message = "You are an expert at scheduling meetings. Your task is to find a suitable time for a meeting based on the participants' schedules and constraints. Follow these rules:\n"
suffix_message = "\nProvide a JSON output of the meeting time range in the exact format: {\"time_range\":\"{12:00:13:00}\"}."

# Initialize the model
# load the base HF model in Kani
engine = HuggingEngine(model_id=args.model)

# outlines wants its tokenizer wrapped in TransformerTokenizer
outlines_tokenizer = outlines.models.TransformerTokenizer(engine.tokenizer)

# create the logits processor
json_logits_processor = outlines.processors.JSONLogitsProcessor(JSON_SCHEMA, outlines_tokenizer)

# and tell kani to pass it to every generate call
engine.hyperparams["logits_processor"] = transformers.LogitsProcessorList([json_logits_processor])

ai = Kani(engine)

# Function to extract the time from the model's response
def extract_time(response):
    match = re.search(r'\{(\d{1,2}:\d{2}:\d{1,2}:\d{2})\}', response)
    if match:
        time_str = f"{{{match.group(1)}}}"  # Keep brackets
        print(time_str)
        return time_str
    else:
        print("No valid time format found")
        return None


# Function to convert the golden plan to dictionary format and remove days of the week
def convert_golden_plan(golden_plan):
   if "Here is the proposed time:" in golden_plan:
       time_part = golden_plan.split(": ")[-1].strip()
       start_time, end_time = time_part.split(" - ")
       start_time = start_time.split(", ")[-1] if ", " in start_time else start_time
       end_time = end_time.split(", ")[-1] if ", " in end_time else end_time
       return f"{{{start_time}:{end_time}}}"
   return None


# Function to calculate accuracy
def calculate_accuracy(expected, predicted):
   correct = 0
   for exp, pred in zip(expected, predicted):
       if exp == pred:
           correct += 1
   return (correct / len(expected)) * 100


# Function to restart the model
def restart_model():
   global ai
   del ai
   torch.cuda.empty_cache()  # Clear GPU cache
   ai = Kani(engine)  # Reinitialize the model


# Function to save checkpoint and current count
def save_checkpoint(index, count):
   with open("checkpoint.txt", "w") as file:
       file.write(f"{index},{count}")


# Function to load checkpoint and current count
def load_checkpoint():
   if os.path.exists("checkpoint.txt"):
       with open("checkpoint.txt", "r") as file:
           index, count = file.read().strip().split(",")
           return int(index), int(count)  # Ensure count continues correctly
   return 0, 1  # Start from 0 index and count 1 if no checkpoint exists


# Main function to run the model
async def run_model():
   expected_outputs = []
   predicted_outputs = []
   start_time = datetime.now()


   # Load checkpoint (index, count)
   start_index, count = load_checkpoint()


   # Only write "Model Results:" if the file is empty
   if os.path.exists("DS-R1-DL-70B_text_results.txt") and os.path.getsize("DS-R1-DL-70B_text_results.txt") == 0:
       with open("DS-R1-DL-70B_text_results.txt", "a") as file:
           file.write("Model Results:\n")


   prompts_list = list(prompts_data.items())


   for i in range(start_index, len(prompts_list)):
       key, data = prompts_list[i]
       prompt_types = [k for k in data.keys() if k.startswith("prompt_0shot")]
       print(prompt_types)
    
       for prompt_type in prompt_types:
           prompt = data[prompt_type]
           print(prompt)
           golden_plan = data["golden_plan"]
           print(golden_plan)


           full_prompt = prefix_message + prompt + suffix_message
           print(full_prompt)


           max_retries = 3
           for retry in range(max_retries):
               try:
                   response = await ai.chat_round_str(full_prompt)
                   print("RAW RESPONSE:", response)
                   predicted_time = extract_time(response)
                   expected_time = convert_golden_plan(golden_plan)


                   expected_outputs.append(expected_time)
                   predicted_outputs.append(predicted_time)


                   timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                   line = f"\n{count}. [{timestamp}] | ANSWER: {predicted_time} EXPECTED: {expected_time}\n"
                   print(line)


                   with open("DS-R1-DL-70B_text_results.txt", "a") as file:
                      file.write(line)


                   count += 1  # Increment the count
                   break  # Exit retry loop if successful
               except RuntimeError as e:
                   print(f"Error occurred (retry {retry + 1}/{max_retries}): {e}")
                   if retry == max_retries - 1:
                       print("Max retries reached. Skipping this prompt.")
                       break
               except Exception as e:
                   print(f"Unexpected error occurred: {e}")
                   break  # Exit retry loop on unexpected errors


           if count % 5 == 0:
               torch.cuda.empty_cache()
               restart_model()


       # Save checkpoint and current count after each prompt
       save_checkpoint(i + 1, count)


   end_time = datetime.now()
   total_time = end_time - start_time


   accuracy = calculate_accuracy(expected_outputs, predicted_outputs)
   accuracy_line = f"\nModel guessed {sum(1 for exp, pred in zip(expected_outputs, predicted_outputs) if exp == pred)} out of {len(expected_outputs)} prompts correctly.\nAccuracy: {accuracy:.2f}%\n"
   print(accuracy_line)
   print(f"Total time taken: {total_time}")


   with open("DS-R1-DL-70B_text_results.txt", "a") as file:
       file.writelines(accuracy_line)
       file.write(f"Total time taken: {total_time}")


# Run the model
asyncio.run(run_model())







