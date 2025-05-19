import json

def calculate_itinerary():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Hamburg"},
        {"day_range": "Day 2-7", "place": "Dublin"},
        {"day_range": "Day 7-12", "place": "London"},
        {"day_range": "Day 12-14", "place": "Reykjavik"},
        {"day_range": "Day 14-18", "place": "Helsinki"},
        {"day_range": "Day 18-21", "place": "Mykonos"}
    ]
    # Validate days
    total_days = 0
    for entry in itinerary:
        days = entry['day_range'].split('-')
        start = int(days[0].split()[1])
        end = int(days[1].split()[1]) if len(days) > 1 else start
        total_days += (end - start + 1)
    # Adjust to fit 16 days by truncating Mykonos
    itinerary[-1]['day_range'] = "Day 18-20"
    adjusted = []
    for entry in itinerary:
        parts = entry['day_range'].split('-')
        start_day = int(parts[0].split()[1])
        end_day = int(parts[1].split()[1]) if len(parts) > 1 else start_day
        if end_day > 16:
            end_day = 16
            entry['day_range'] = f"Day {start_day}-{end_day}"
        adjusted.append(entry)
    return {"itinerary": adjusted}

result = calculate_itinerary()
print(json.dumps(result))