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
            "pattern": "^\"\"\\n'''python\\n([\\s\\S]+)\\n'''\\n\"\"\"$"
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
Generate a response in the following JSON format. Ensure the code starts with '''python and ends with ''' to encase the code. Use proper indentation and spacing.

Finally, make sure the output of the program you generate displays the calculated time in the following format: {HH:MM:HH:MM}.

Here is an example of a possible format of time: {14:30:15:30}.

The final time must be encased in curly brackets: {}."""

prompt1 = """You are an expert at scheduling meetings. You are given a few constraints on the existing schedule of each participant, the meeting duration, and possibly some preferences on the meeting time. Note there exists a solution that works with existing schedule of every participant. Here are a few example tasks and solutions:

TASK: You need to schedule a meeting for Raymond, Billy and Donald for half an hour between the work hours of 9:00 to 17:00 on Monday. 

Here are the existing schedules for everyone during the day: 
Raymond has blocked their calendar on Monday during 9:00 to 9:30, 11:30 to 12:00, 13:00 to 13:30, 15:00 to 15:30; 
Billy has meetings on Monday during 10:00 to 10:30, 12:00 to 13:00, 16:30 to 17:00; 
Donald has meetings on Monday during 9:00 to 9:30, 10:00 to 11:00, 12:00 to 13:00, 14:00 to 14:30, 16:00 to 17:00; 

Billy would like to avoid more meetings on Monday after 15:00. Find a time that works for everyone's schedule and constraints. 
SOLUTION: 

Please generate a full Python script program which calculates the proposed time. Ensure the code is clean, well-formatted, and free from unnecessary escape characters or tags. 
Generate a response in the following JSON format. Ensure the code starts with '''python and ends with ''' to encase the code. Use proper indentation and spacing.

Finally, make sure the output of the program you generate displays the calculated time in the following format: {HH:MM:HH:MM}.

Here is an example of a possible format of time: {14:30:15:30}.

The final time must be encased in curly brackets: {}."""

async def get_model_response(prompt):
    response = await ai.chat_round_str(prompt)
    return response

def extract_code(model_response):
    """
    Extract the code block from the model response.
    The code is expected to be wrapped in triple quotes and start with '''python.
    """
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

def parse_output(output):
    """
    Parse the output to find the time in the format {HH:MM:HH:MM}.
    If the format is correct, return it as the true answer; otherwise, return None.
    """
    match = re.search(r"\{(\d{2}:\d{2}:\d{2}:\d{2})\}", output)
    if match:
        return match.group(0)
    else:
        return None

async def main():
    for prompt in [prompt0, prompt1]:
        model_response = await get_model_response(prompt)  # Await the coroutine
        print("\nModel Response:\n\n", model_response)
        print("\n***************************************\n")
    
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
        if output:
            print("Generated Code Output:\n", output)
            # Parse the output to find the true answer
            true_answer = parse_output(output)
            if true_answer:
                print("\nTrue Answer:\n", true_answer)
            else:
                print("\nTrue Answer:\n The output does not contain the correct format {HH:MM:HH:MM}.")
        else:
            print("Generated Code Output:\n None")

# Run the main function
asyncio.run(main())

# import asyncio
# import outlines
# import transformers
# import argparse
# import re
# import json
# import subprocess
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
#             "pattern": "^\"\"\\n'''python\\n([\\s\\S]+)\\n'''\\n\"\"\"$"
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
# Generate a response in the following JSON format. Ensure the code is enclosed within double quotes in the beginning (\"\") and triple quotes at the end, and starts with '''python. Use proper indentation and spacing.

# Finally, make sure the output of the program you generate displays the calculated time in the following format: {HH:MM:HH:MM}.

# Here is an example of a possible format of time: {14:30:15:30}.

# The final time must be encased in curly brackets: {}."""

# prompt1 = """You are an expert at scheduling meetings. You are given a few constraints on the existing schedule of each participant, the meeting duration, and possibly some preferences on the meeting time. Note there exists a solution that works with existing schedule of every participant. Here are a few example tasks and solutions:

# TASK: You need to schedule a meeting for Raymond, Billy and Donald for half an hour between the work hours of 9:00 to 17:00 on Monday. 

# Here are the existing schedules for everyone during the day: 
# Raymond has blocked their calendar on Monday during 9:00 to 9:30, 11:30 to 12:00, 13:00 to 13:30, 15:00 to 15:30; 
# Billy has meetings on Monday during 10:00 to 10:30, 12:00 to 13:00, 16:30 to 17:00; 
# Donald has meetings on Monday during 9:00 to 9:30, 10:00 to 11:00, 12:00 to 13:00, 14:00 to 14:30, 16:00 to 17:00; 

# Billy would like to avoid more meetings on Monday after 15:00. Find a time that works for everyone's schedule and constraints. 
# SOLUTION: 

# Please generate a full Python script program which calculates the proposed time. Ensure the code is clean, well-formatted, and free from unnecessary escape characters or tags. 
# Generate a response in the following JSON format. Ensure the code is enclosed within double quotes in the beginning (\"\") and triple quotes at the end, and starts with '''python. Use proper indentation and spacing.

# Finally, make sure the output of the program you generate displays the calculated time in the following format: {HH:MM:HH:MM}.

# Here is an example of a possible format of time: {14:30:15:30}.

# The final time must be encased in curly brackets: {}."""

# async def get_model_response(prompt):
#     response = await ai.chat_round_str(prompt)
#     return response

# def extract_code(model_response):
#     """
#     Extract the code block from the model response.
#     The code is expected to be wrapped in triple quotes and start with '''python.
#     """
#     match = re.search(r"'''python\n([\s\S]+?)\n'''", model_response)
#     if match:
#         code = match.group(1)
#     else:
#         raise ValueError("Could not extract code from the model response.")
    
#     return code

# def write_code_to_file(code, filename="generated_code.py"):
#     with open(filename, "w") as f:
#         f.write(code)

# def run_generated_code(filename="generated_code.py"):
#     result = subprocess.run(["python", filename], capture_output=True, text=True)
#     return result.stdout

# async def main():
#     for prompt in [prompt0, prompt1]:
#         model_response = await get_model_response(prompt)  # Await the coroutine
#         print("\nModel Response:\n\n", model_response)
#         print("\n***************************************\n")
    
#         # Extract the code from the model response
#         try:
#             code = extract_code(model_response)
#         except ValueError as e:
#             print(f"Error: {e}")
#             return
        
#         # Write the code to a file
#         write_code_to_file(code)
        
#         # Run the generated code and capture the output
#         output = run_generated_code()
        
#         # Print the output
#         if output != None:
#             print("Generated Code Output:\n", output)
#         else:
#             print("Generated Code Output:\n None")

# # Run the main function
# asyncio.run(main())





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



