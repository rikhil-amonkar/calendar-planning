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
        response_format={"type": "json_object"}
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
        Your job is to plan the meeting schedule to meet people at certain locations and times outputted in JSON format based on a description. Here's an example description:\n
        TASK: You are visiting Philadelphia for the day and want to meet as many friends as possible. Solve the problem by considering various different schedules and picking the best one to optimize your goals.\n\nTravel distances (in minutes):\nDrexel University to 30th Street Station: 8.\nDrexel University to Market Street: 12.\n30th Street Station to Drexel University: 10.\n30th Street Station to Market Street: 7.\nMarket Street to Drexel University: 15.\nMarket Street to 30th Street Station: 9.\n\nCONSTRAINTS: You arrive at Drexel University at 9:00AM. Harry will be at 30th Street Station from 2:00PM to 3:30PM. You'd like to meet Harry for a minimum of 60 minutes. Ronan will be at Market Street from 12:00PM to 2:00PM. You'd like to meet Ronan for a minimum of 30 minutes.\n\nYour response should start with 'SOLUTION:'.\n
        Here is the corresponding output JSON:\n
        {{
            "meeting_planning_example_harry_crafted": {{
                "input_query": [
                    "You are visiting Philadelphia for the day and want to meet as many friends as possible. Solve the problem by considering various different schedules and picking the best one to optimize your goals.\n\nTravel distances (in minutes):\nDrexel University to 30th Street Station: 8.\nDrexel University to Market Street: 12.\n30th Street Station to Drexel University: 10.\n30th Street Station to Market Street: 7.\nMarket Street to Drexel University: 15.\nMarket Street to 30th Street Station: 9.\n\nCONSTRAINTS: You arrive at Drexel University at 9:00AM. Harry will be at 30th Street Station from 2:00PM to 3:30PM. You'd like to meet Harry for a minimum of 60 minutes. Ronan will be at Market Street from 12:00PM to 2:00PM. You'd like to meet Ronan for a minimum of 30 minutes.\n\nYour response should start with 'SOLUTION:'."
                ],
                "travel_distances": [
                    {{
                        "place": {{ "from": "Drexel University", "to": "30th Street Station" }},
                        "walking_time": 8
                    }},
                    {{
                        "place": {{ "from": "Drexel University", "to": "Market Street" }},
                        "walking_time": 12
                    }},
                    {{
                        "place": {{ "from": "30th Street Station", "to": "Drexel University" }},
                        "walking_time": 10
                    }},
                    {{
                        "place": {{ "from": "30th Street Station", "to": "Market Street" }},
                        "walking_time": 7
                    }},
                    {{
                        "place": {{ "from": "Market Street", "to": "Drexel University" }},
                        "walking_time": 15
                    }},
                    {{
                        "place": {{ "from": "Market Street", "to": "30th Street Station" }},
                        "walking_time": 9
                    }}
                ],
                "constraints": [
                    {{
                        "location": "Drexel University",
                        "time_of_day": 9
                    }},
                    {{
                        "person": "Harry",
                        "location": "30th Street Station",
                        "duration": {{ "from": 14, "to": 15.5 }},
                        "min_meeting_duration": 60
                    }},
                    {{
                        "person": "Ronan",
                        "location": "Market Street",
                        "duration": {{ "from": 12, "to": 14 }},
                        "min_meeting_duration": 30
                    }}
                ]
            }}
        }}

        \n
        Now you try it. Your job is to plan the best meeting schedule when you can meet people at certain locations and times outputted in JSON format based on a description. IMPORTANT: The top-level JSON key must be "{example_id}". Here's an example description:\n
        {prompt}
        """

        print(full_prompt)

        # Retry mechanism: Try up to 3 times if the response fails
        retries = 3
        for attempt in range(retries):
            try:
                model_response = asyncio.run(get_model_response(full_prompt))
                print(model_response)
                
                # Save the parsed JSON response directly
                output_file_path = os.path.join(output_folder, f"{example_id}_output.json")
                with open(output_file_path, 'w') as json_file:
                    json.dump(model_response, json_file, indent=4)
                break  # Exit the retry loop if successful
                
            except Exception as e:
                print(f"Error processing example {example_id} on attempt {attempt + 1}: {str(e)}")
                if attempt == retries - 1:  # Last attempt, move on to the next example
                    print(f"Failed to process example {example_id} after {retries} attempts.")
                    continue

if __name__ == "__main__":
    examples_file = '../../data/meeting_planning_100.json'
    output_folder = 'meeting'
    process_examples(examples_file, output_folder)
