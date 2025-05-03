import json
import random

# Load the data
for task in ["calendar_scheduling", "trip_planning", "meeting_planning"]:
    with open(f'../natural-plan/data/{task}.json', 'r', encoding='utf-8') as f:
        data = json.load(f)

    # Randomly sample 100 examples
    sampled = dict(random.sample(list(data.items()), 100))

    # Save the sampled examples
    with open(f'../data/{task}_100.json', 'w', encoding='utf-8') as f:
        json.dump(sampled, f, ensure_ascii=False, indent=2)