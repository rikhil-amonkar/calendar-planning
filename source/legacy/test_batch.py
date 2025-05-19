import json
import time
import requests

API_KEY = json.load(open("../../scheduling_key.json"))["openai"]
HEADERS = {"Authorization": f"Bearer {API_KEY}"}
API_BASE = "https://api.openai.com/v1"

prompts = [
    "What is 1+1?",
    "What is the capital of France?",
    "What is the largest mammal?"
]

# 1. Write prompts to JSONL file
input_file = "batch_input.jsonl"
with open(input_file, "w") as f:
    for prompt in prompts:
        f.write(json.dumps({
            "custom_id": prompt[:20],  # Optional: for tracking
            "messages": [{"role": "user", "content": prompt}]
        }) + "\n")

# 2. Upload file
with open(input_file, "rb") as f:
    files = {"file": (input_file, f, "application/jsonl")}
    res = requests.post(f"{API_BASE}/files", headers=HEADERS, files=files)
    res.raise_for_status()
    file_id = res.json()["id"]

# 3. Create batch job
batch_req = {
    "input_file_id": file_id,
    "endpoint": "/v1/chat/completions",
    "completion_window": "24h",
    "parameters": {
        "model": "gpt-4.1-nano",
        "temperature": 0,
        "max_tokens": 50,
        "top_p": 1
    }
}
res = requests.post(f"{API_BASE}/batches", headers={**HEADERS, "Content-Type": "application/json"}, data=json.dumps(batch_req))
res.raise_for_status()
batch_id = res.json()["id"]
print(f"Batch job submitted: {batch_id}")

# 4. Poll for completion
while True:
    res = requests.get(f"{API_BASE}/batches/{batch_id}", headers=HEADERS)
    res.raise_for_status()
    status = res.json()["status"]
    print(f"Batch status: {status}")
    if status in ("completed", "failed", "expired", "canceled"):
        break
    time.sleep(10)

if status != "completed":
    print("Batch did not complete successfully.")
    exit(1)

# 5. Download output file
output_file_id = res.json()["output_file_id"]
res = requests.get(f"{API_BASE}/files/{output_file_id}/content", headers=HEADERS)
res.raise_for_status()
results = [json.loads(line) for line in res.text.strip().split("\n")]

# 6. Print results
for i, result in enumerate(results):
    answer = result["response"]["choices"][0]["message"]["content"]
    print(f"Prompt: {prompts[i]}")
    print(f"Response: {answer}\n")