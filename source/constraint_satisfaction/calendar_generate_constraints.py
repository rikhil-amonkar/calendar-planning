import json
import os
import asyncio
from openai import AsyncOpenAI

# Read the API key and initialize client (same as before)
with open('/home/rma336/openai_research/openai_api_key.txt', 'r') as key_file:
    api_key = key_file.read().strip()

client = AsyncOpenAI(api_key=api_key)

async def get_model_response(full_prompt):
    response = await client.chat.completions.create(
        model='gpt-4.1-nano',
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

        TASK: You need to schedule a meeting for Rikhil and Harry for one hour between the work hours of 9:00 to 17:00 on either Monday or Tuesday. \n\nHere are the existing schedules for everyone during these days: \nHarry can only meet before 11:00 or after 12:00 on Monday, or any time on Tuesday; \nRikhil has blocked their calendar on Monday during 9:00 to 9:30 and 11:30 to 12:00 on Tuesday; \n\nHarry prefers to meet after noon; Rikhil would like to avoid meetings on Tuesday before 11:00. Find the earliest time that works for everyone's schedule and constraints.\n

        Here is the corresponding output JSON:\n

        {{
            "calendar_scheduling_example_harry_crafted": {{
            "input_query": [
                "TASK: You need to schedule a meeting for Rikhil and Harry for one hour between the work hours of 9:00 to 17:00 on either Monday or Tuesday. \n\nHere are the existing schedules for everyone during these days: \nHarry can only meet before 11:00 or after 12:00 on Monday, or any time on Tuesday; \nRikhil has blocked their calendar on Monday during 9:00 to 9:30 and 11:30 to 12:00 on Tuesday; \n\nHarry prefers to meet after noon; Rikhil would like to avoid meetings on Tuesday before 11:00. Find the earliest time that works for everyone's schedule and constraints."
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
            ],
            "unpreferred_ranges": [
                {{
                "day": "Tuesday",
                "start": 0,
                "end": 11
                }}
            ]
            }}
        }}

        \n
        Now you try it. Your job is to extract the time when people are unavailable in JSON based on a description. IMPORTANT: The top-level JSON key must be "{example_id}". Here's an example description:\n

        {prompt}
        """

        try:
            model_response = asyncio.run(get_model_response(full_prompt))
            
            # Save the parsed JSON response directly
            output_file_path = os.path.join(output_folder, f"{example_id}_output.json")
            with open(output_file_path, 'w') as json_file:
                json.dump(model_response, json_file, indent=4)
                
        except Exception as e:
            print(f"Error processing example {example_id}: {str(e)}")
            continue

if __name__ == "__main__":
    examples_file = '../../data/calendar_scheduling_100.json'
    output_folder = 'calendar'
    process_examples(examples_file, output_folder)