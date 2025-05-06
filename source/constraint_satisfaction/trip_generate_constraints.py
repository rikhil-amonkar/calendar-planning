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
        model='gpt-4.1',
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

        Your job is to plan a trip based on locations and days outputted in a JSON format based on a description. Here's an example description:

        TASK: You plan to visit 3 European cities for 14 days in total. You only take direct flights to commute between cities. You would like to visit Paris for 6 days. You want to meet a friend in Paris between day 9 and day 14. You would like to visit London for 5 days. You would like to visit Rome for 5 days.\n\nHere are the cities that have direct flights:\nLondon and Paris, Rome and London.\n\nFind a trip plan of visiting the cities for 14 days by taking direct flights to commute between them.\n

        Here is the corresponding output JSON:\n

        {{
            "trip_planning_example_harry_crafted": {{
                "input_query": [
                    "You plan to visit 3 European cities for 14 days in total. You only take direct flights to commute between cities. You would like to visit Paris for 6 days. You want to meet a friend in Paris between day 9 and day 14. You would like to visit London for 5 days. You would like to visit Rome for 5 days.\n\nHere are the cities that have direct flights:\nLondon and Paris, Rome and London.\n\nFind a trip plan of visiting the cities for 14 days by taking direct flights to commute between them."
                ],
                "trip_length": 14,
                "city_length": [
                    {{
                        "city": "Paris",
                        "days": 6
                    }},
                    {{
                        "city": "London",
                        "days": 5
                    }},
                    {{
                        "city": "Rome",
                        "days": 5
                    }}
                ],
                "city_day_ranges": [
                    {{
                        "city": "Paris",
                        "start": 9,
                        "end": 14
                }}
                ],
                "direct_flights": [
                    {{"from": "London", "to": "Paris"}},
                    {{"from": "Rome", "to": "London"}}
                ]
            }}
        }}

        \n
        Now you try it. Your job is to plan a trip based on locations and days outputted in a JSON format based on a description. IMPORTANT: The top-level JSON key must be "{example_id}". Here's an example description:\n

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
    examples_file = '../../data/trip_planning_100.json'
    output_folder = 'trip'
    process_examples(examples_file, output_folder)