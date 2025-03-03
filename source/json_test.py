import asyncio
import outlines
import transformers
import argparse
import re
import json
import subprocess
from kani import Kani
from kani.engines import WrapperEngine
from kani.engines.huggingface import HuggingEngine

# Define the JSON schema for the output
JSON_SCHEMA = {
    "type": "object",
    "properties": {
        "explanation": {
            "type": "string"
        },
        "code": {
            "type": "string",
            "pattern": "^\"\"\"\\n'''python\\n([\\s\\S]+)\\n'''\\n\"\"\"$"
        }
    },
    "required": ["explanation", "code"]
}

# Argument parser to select the model
parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
args = parser.parse_args()

class JSONGuidanceHFWrapper(WrapperEngine):
    def __init__(self, engine: HuggingEngine, *args, json_schema, **kwargs):
        super().__init__(engine, *args, **kwargs)
        # keep a reference to the JSON schema we want to use
        self.engine: HuggingEngine  # type hint for IDEs
        self.json_schema = json_schema
        self.outlines_tokenizer = outlines.models.TransformerTokenizer(self.engine.tokenizer)

    def _create_logits_processor(self):
        json_logits_processor = outlines.processors.JSONLogitsProcessor(self.json_schema, self.outlines_tokenizer)
        return transformers.LogitsProcessorList([json_logits_processor])

    async def predict(self, *args, **kwargs):
        # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
        if "logits_processor" not in kwargs:
            kwargs["logits_processor"] = self._create_logits_processor()
        return await super().predict(*args, **kwargs)

    async def stream(self, *args, **kwargs):
        # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
        if "logits_processor" not in kwargs:
            kwargs["logits_processor"] = self._create_logits_processor()
        async for elem in super().stream(*args, **kwargs):
            yield elem

# Load the model selected by the user
model = HuggingEngine(model_id=args.model)
engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)

# Create the Kani instance
ai = Kani(engine)

prompt0 = """You are an expert at scheduling meetings. You are given a few constraints on the existing schedule of each participant, the meeting duration, and possibly some preferences on the meeting time. Note there exists a solution that works with existing schedule of every participant. Here are a few example tasks and solutions:

TASK: You need to schedule a meeting for Michelle, Steven and Jerry for one hour between the work hours of 9:00 to 17:00 on Monday. 

Here are the existing schedules for everyone during the day: 
Michelle has meetings on Monday during 11:00 to 12:00; 
Steven has blocked their calendar on Monday during 9:00 to 9:30, 11:30 to 12:00, 13:30 to 14:00, 15:30 to 16:00; 
Jerry has blocked their calendar on Monday during 9:00 to 9:30, 10:00 to 11:00, 11:30 to 12:30, 13:00 to 14:30, 15:30 to 16:00, 16:30 to 17:00; 

Find a time that works for everyone's schedule and constraints. 
SOLUTION: 

Please generate a full Python script program which calculates the proposed time. Ensure the code is clean, well-formatted, and free from unnecessary escape characters or tags. 
Generate a response in the following JSON format. Ensure the code is enclosed within triple quotes (\"\"\") and starts with '''python. Use proper indentation and spacing."""

async def get_model_response(prompt):
    response = await ai.chat_round_str(prompt)
    return response

def preprocess_response(model_response):
    """
    Preprocess the model response to make it valid JSON.
    """
    # Replace triple quotes with escaped double quotes
    model_response = model_response.replace('"""', '\\"\\"\\"')
    return model_response

def extract_code(model_response):
    try:
        # Preprocess the response to make it valid JSON
        model_response = preprocess_response(model_response)
        
        # Try to parse the response as JSON
        response_dict = json.loads(model_response)
        code = response_dict["code"]
    except json.JSONDecodeError:
        # If JSON parsing fails, use regex to extract the code block
        match = re.search(r"'''python\n([\s\S]+?)\n'''", model_response)
        if match:
            code = match.group(1)
        else:
            raise ValueError("Could not extract code from the model response.")
    
    return code

def write_code_to_file(code, filename="generated_code.py"):
    with open(filename, "w") as f:
        f.write(code)

def run_generated_code(filename="generated_code.py"):
    result = subprocess.run(["python", filename], capture_output=True, text=True)
    return result.stdout

async def main():
    model_response = await get_model_response(prompt0)
    print("Model Response:", model_response)
    
    # Extract the code from the model response
    try:
        code = extract_code(model_response)
    except ValueError as e:
        print(f"Error: {e}")
        return
    
    # Write the code to a file
    write_code_to_file(code)
    
    # Run the generated code and capture the output
    output = run_generated_code()
    
    # Print the output
    print("Generated Code Output:", output)

# Run the main function
asyncio.run(main())







# import asyncio
# import outlines
# import transformers
# import argparse
# import re
# import json
# import ast
# from kani import Kani
# from kani.engines import WrapperEngine
# from kani.engines.huggingface import HuggingEngine

# # Define the JSON schema for the output
# JSON_SCHEMA = {
#     "type": "object",
#     "properties": {
#         "explanation": {
#             "type": "string"
#         },
#         "code": {
#             "type": "string",
#             "pattern": "^\"\"\"\\n'''python\\n([\\s\\S]+)\\n'''\\n\"\"\"$"
#         }
#     },
#     "required": ["explanation", "code"]
# }


# # Argument parser to select the model
# parser = argparse.ArgumentParser(description="Select a HuggingFace model.")
# parser.add_argument('--model', type=str, required=True, help="The HuggingFace model ID to use.")
# args = parser.parse_args()

# class JSONGuidanceHFWrapper(WrapperEngine):
#     def __init__(self, engine: HuggingEngine, *args, json_schema, **kwargs):
#         super().__init__(engine, *args, **kwargs)
#         # keep a reference to the JSON schema we want to use
#         self.engine: HuggingEngine  # type hint for IDEs
#         self.json_schema = json_schema
#         self.outlines_tokenizer = outlines.models.TransformerTokenizer(self.engine.tokenizer)

#     def _create_logits_processor(self):
#         json_logits_processor = outlines.processors.JSONLogitsProcessor(self.json_schema, self.outlines_tokenizer)
#         return transformers.LogitsProcessorList([json_logits_processor])

#     async def predict(self, *args, **kwargs):
#         # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         return await super().predict(*args, **kwargs)

#     async def stream(self, *args, **kwargs):
#         # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         async for elem in super().stream(*args, **kwargs):
#             yield elem


# # Load the model selected by the user
# model = HuggingEngine(model_id=args.model)
# engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)

# # Create the Kani instance
# ai = Kani(engine)

# prompt0 = """You are an expert at scheduling meetings. You are given a few constraints on the existing schedule of each participant, the meeting duration, and possibly some preferences on the meeting time. Note there exists a solution that works with existing schedule of every participant. Here are a few example tasks and solutions:

# TASK: You need to schedule a meeting for Michelle, Steven and Jerry for one hour between the work hours of 9:00 to 17:00 on Monday. 

# Here are the existing schedules for everyone during the day: 
# Michelle has meetings on Monday during 11:00 to 12:00; 
# Steven has blocked their calendar on Monday during 9:00 to 9:30, 11:30 to 12:00, 13:30 to 14:00, 15:30 to 16:00; 
# Jerry has blocked their calendar on Monday during 9:00 to 9:30, 10:00 to 11:00, 11:30 to 12:30, 13:00 to 14:30, 15:30 to 16:00, 16:30 to 17:00; 

# Find a time that works for everyone's schedule and constraints. 
# SOLUTION: 

# Please generate a full Python script program which calculates the proposed time. Ensure the code is clean, well-formatted, and free from unnecessary escape characters or tags. 
# Generate a response in the following JSON format. Ensure the code is enclosed within triple quotes (\"\"\") and starts with '''python. Use proper indentation and spacing."""

# async def get_model_response(prompt):
#     response = await ai.chat_round_str(prompt)
#     return response

# model_response = asyncio.run(get_model_response(prompt0))
# print(model_response)




#************JSON TEST FOR TEXT OUTPUTS***********************

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

# # Define the JSON schema for the time range output
# JSON_SCHEMA = {
#     "type": "object",
#     "properties": {
#         "time_range": {
#             "type": "string",
#             "pattern": "^\\{\\d{2}:\\d{2}:\\d{2}:\\d{2}\\}$"
#         }
#     },
#     "required": ["time_range"],
# }

# class JSONGuidanceHFWrapper(WrapperEngine):
#     def __init__(self, engine: HuggingEngine, *args, json_schema, **kwargs):
#         super().__init__(engine, *args, **kwargs)
#         # keep a reference to the JSON schema we want to use
#         self.engine: HuggingEngine  # type hint for IDEs
#         self.json_schema = json_schema
#         self.outlines_tokenizer = outlines.models.TransformerTokenizer(self.engine.tokenizer)

#     def _create_logits_processor(self):
#         json_logits_processor = outlines.processors.JSONLogitsProcessor(self.json_schema, self.outlines_tokenizer)
#         return transformers.LogitsProcessorList([json_logits_processor])

#     async def predict(self, *args, **kwargs):
#         # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         return await super().predict(*args, **kwargs)

#     async def stream(self, *args, **kwargs):
#         # each time we call predict or stream, pass a new instance of JSONLogitsProcessor
#         if "logits_processor" not in kwargs:
#             kwargs["logits_processor"] = self._create_logits_processor()
#         async for elem in super().stream(*args, **kwargs):
#             yield elem

# model = HuggingEngine(model_id="meta-llama/Meta-Llama-3.1-8B-Instruct")
# engine = JSONGuidanceHFWrapper(model, json_schema=JSON_SCHEMA)

# # Create the Kani instance
# ai = Kani(engine)

# prompt0 = """You are an expert at scheduling meetings. You are given a few constraints on the existing schedule of each participant, the meeting duration, and possibly some preferences on the meeting time. Note there exists a solution that works with existing schedule of every participant. Here are a few example tasks and solutions:

# TASK: You need to schedule a meeting for Michelle, Steven and Jerry for one hour between the work hours of 9:00 to 17:00 on Monday. 

# Here are the existing schedules for everyone during the day: 
# Michelle has meetings on Monday during 11:00 to 12:00; 
# Steven has blocked their calendar on Monday during 9:00 to 9:30, 11:30 to 12:00, 13:30 to 14:00, 15:30 to 16:00; 
# Jerry has blocked their calendar on Monday during 9:00 to 9:30, 10:00 to 11:00, 11:30 to 12:30, 13:00 to 14:30, 15:30 to 16:00, 16:30 to 17:00; 

# Find a time that works for everyone's schedule and constraints. 
# SOLUTION: 

# Please output the proposed time in the following JSON format:
# {"time_range": "{HH:MM:HH:MM}"}. For example, if the proposed time is 14:30 to 15:30, the output should be:
# {"time_range": "{14:30:15:30}"}"""

# prompt1 = """You are an expert at scheduling meetings. You are given a few constraints on the existing schedule of each participant, the meeting duration, and possibly some preferences on the meeting time. Note there exists a solution that works with existing schedule of every participant. Here are a few example tasks and solutions:

# TASK: You need to schedule a meeting for Raymond, Billy and Donald for half an hour between the work hours of 9:00 to 17:00 on Monday. 

# Here are the existing schedules for everyone during the day: 
# Raymond has blocked their calendar on Monday during 9:00 to 9:30, 11:30 to 12:00, 13:00 to 13:30, 15:00 to 15:30; 
# Billy has meetings on Monday during 10:00 to 10:30, 12:00 to 13:00, 16:30 to 17:00; 
# Donald has meetings on Monday during 9:00 to 9:30, 10:00 to 11:00, 12:00 to 13:00, 14:00 to 14:30, 16:00 to 17:00; 

# Billy would like to avoid more meetings on Monday after 15:00. Find a time that works for everyone's schedule and constraints. 
# SOLUTION: 

# Please output the proposed time in the following JSON format:
# {"time_range": "{HH:MM:HH:MM}"}. For example, if the proposed time is 14:30 to 15:30, the output should be:
# {"time_range": "{14:30:15:30}"}"""

# async def get_model_response(prompt):
#     response = await ai.chat_round_str(prompt)
#     return response  # Return the actual response

# # model_response = asyncio.run(get_model_response(prompt0))
# # print(model_response)

# # model_response = asyncio.run(get_model_response(prompt1))
# # print(model_response)

# for prompt in [prompt0, prompt1]:
#     model_response = asyncio.run(get_model_response(prompt))
#     print(model_response)



