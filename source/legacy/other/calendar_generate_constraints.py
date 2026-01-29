import json
import os
import asyncio
from openai import AsyncOpenAI

# Read the API key and initialize client (same as before)
with open('<YOUR_API_KEY_PATH>', 'r') as key_file:  # Replace with path to your OpenAI API key file
    api_key = key_file.read().strip()

client = AsyncOpenAI(api_key=api_key)

async def get_model_response(full_prompt):
    response = await client.chat.completions.create(
        model='gpt-4.1-mini',
        messages=[
            {"role": "system", "content": "You are a helpful assistant."},
            {"role": "user", "content": full_prompt}
        ],
        response_format={ "type": "json_object" }  # Request JSON response format
    )
    
    # Get the content and parse it as JSON
    model_response = response.choices[0].message.content.strip()
    return json.loads(model_response)  # Parse the JSON string into a Python dict

def process_examples(examples_file, output_folder):
    with open(examples_file, 'r') as file:
        calendar_examples = json.load(file)

    if not os.path.exists(output_folder):
        os.makedirs(output_folder)

    for example_id, example in calendar_examples.items():
        prompt = example['prompt_0shot']
        
        full_prompt = f"""

        Your job is to extract the time when people are unavailable in JSON based on a description. Here's an example description:\n

        You are an expert at scheduling meetings. You are given a few constraints on the existing schedule of each participant, the meeting duration, and possibly some preferences on the meeting time. Note there exists a solution that works with existing schedule of every participant. Here are a few example tasks and solutions:\n

        TASK: You need to schedule a meeting for personA and personB for one hour between the work hours of 9:00 to 17:00 on either Monday or Tuesday. \n\nHere are the existing schedules for everyone during these days: \npersonB can only meet before 11:00 or after 12:00 on Monday, or any time on Tuesday; \npersonA has blocked their calendar on Monday during 9:00 to 9:30 and 11:30 to 12:00 on Tuesday; \n\npersonB prefers to meet after noon; personA would like to avoid meetings on Tuesday before 11:00. Find the earliest time that works for everyone's schedule and constraints.\n

        Here is the corresponding output JSON:\n

        {{
            "calendar_scheduling_example_personB_crafted": {{
            "input_query": [
                "TASK: You need to schedule a meeting for personA and personB for one hour between the work hours of 9:00 to 17:00 on either Monday or Tuesday. \n\nHere are the existing schedules for everyone during these days: \npersonB can only meet before 11:00 or after 12:00 on Monday, or any time on Tuesday; \npersonA has blocked their calendar on Monday during 9:00 to 9:30 and 11:30 to 12:00 on Tuesday; \n\npersonB prefers to meet after noon; personA would like to avoid meetings on Tuesday before 11:00. Find the earliest time that works for everyone's schedule and constraints."
            ],
            "allowed_ranges": [
                {{
                "day": "Monday",
                "start": 0,
                "end": 11
                }},
                {{
                "day": "Monday",
                "start": 12,
                "end": 24
                }},
                {{
                "day": "Tuesday",
                "start": 0,
                "end": 24
                }}
            ],
            "disallowed_ranges": [
                {{
                "day": "Monday",
                "start": 9,
                "end": 9.5
                }},
                {{
                "day": "Tuesday",
                "start": 11.5,
                "end": 12
                }}
            ],
            "optimization": "earliest",
            "preferred_ranges": [
                {{
                "day": "Monday",
                "start": 12,
                "end": 24
                }},
                {{
                "day": "Tuesday",
                "start": 12,
                "end": 24
                }}
