import json
from openai import OpenAI

# Load the API key from a file anywhere on your system
with open("/local-ssd/rma336/openai_research/deepseek_api_key.json") as f:
    keys = json.load(f)

client = OpenAI(api_key=keys["openai"])

response = client.chat.completions.create(
    model="gpt-5-2025-08-07",
    messages=[
        {"role": "system", "content": "You are a helpful assistant."},
        {"role": "user", "content": "Give me 3 fun facts about space."}
    ]
)

print(response.choices[0].message.content)
