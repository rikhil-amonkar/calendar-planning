import asyncio
import outlines
import transformers
import argparse
import re
import json
import ast
from kani import Kani
from kani.engines import WrapperEngine
from kani.engines.huggingface import HuggingEngine

# Define the JSON schema for the output
JSON_SCHEMA = {
    "type": "object",
    "properties": {
        "text": {"type": "string"},
        "code": {"type": "string"}
    },
    "required": ["text", "code"],
    "additionalProperties": False,
    "description": "The output should contain any text separate from code which is clean, well-formatted Python."
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

Please generate a full Python script program which calculates the proposed time. Ensure the code is clean, well-formatted, and free from unnecessary escape characters or tags. Output your code and text in the JSON format as follows:

"""

async def get_model_response(prompt):
    response = await ai.chat_round_str(prompt)
    return response

def format_python_code(code_str):
    # Remove triple backticks if present
    code_str = re.sub(r'```python', '', code_str).strip()
    
    # Replace escaped newlines and other escaped characters
    formatted_code = code_str.encode().decode('unicode_escape')
    
    try:
        # Parse the formatted string into an AST (Abstract Syntax Tree)
        parsed_code = ast.parse(formatted_code)
        # Convert the AST back into formatted Python code
        formatted_code = ast.unparse(parsed_code)
        formatted_code = re.sub(r'\n{2,}', '\n\n', formatted_code)  # Normalize extra newlines
        formatted_code = re.sub(r'\s+\n', '\n', formatted_code)  # Remove unnecessary leading spaces
        formatted_code = re.sub(r'\t', '    ', formatted_code)  # Replace tabs with spaces
        return formatted_code
    except SyntaxError as e:
        return f"Syntax Error: {e}"

def extract_code_from_json(model_response):
    try:
        model_response_json = json.loads(model_response)
        return model_response_json.get("code", "")
    except json.JSONDecodeError as e:
        print(f"Error decoding JSON: {e}")
        return ""

async def main():
    model_response = await get_model_response(prompt0)
    print("Model Response:", model_response)
    
    # Extract the code from the JSON response
    code = extract_code_from_json(model_response)
    if code:
        print("Raw Code:\n", code)
        # Format the extracted code
        formatted_code = format_python_code(code)
        print("Formatted Code:\n", formatted_code)
    else:
        print("No code found in the response.")

# Run the main function
asyncio.run(main())



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



