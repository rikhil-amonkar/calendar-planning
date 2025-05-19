import json

def calculate_itinerary():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Brussels"},
        {"day_range": "Day 2-4", "place": "London"},
        {"day_range": "Day 5-7", "place": "Venice"},
        {"day_range": "Day 7-11", "place": "Madrid"},
        {"day_range": "Day 11-14", "place": "Santorini"},
        {"day_range": "Day 14-17", "place": "Lisbon"},
        {"day_range": "Day 17", "place": "Reykjavik"}
    ]
    
    # Validate constraints
    days = {city: 0 for city in ["Brussels", "London", "Venice", "Madrid", "Santorini", "Lisbon", "Reykjavik"]}
    for entry in itinerary:
        parts = entry['day_range'].split('-')
        start = int(parts[0].split()[1])
        end = int(parts[1].split()[1]) if len(parts) > 1 else start
        days[entry['place']] += end - start + 1
    
    assert days["Brussels"] == 2, "Brussels days mismatch"
    assert days["London"] == 3, "London days mismatch"
    assert days["Venice"] == 3, "Venice days mismatch"
    assert days["Madrid"] == 5, "Madrid days mismatch"
    assert days["Santorini"] == 3, "Santorini days mismatch"
    assert days["Lisbon"] == 4, "Lisbon days mismatch"
    assert days["Reykjavik"] == 1, "Reykjavik days mismatch"
    
    return {"itinerary": itinerary}

print(json.dumps(calculate_itinerary(), indent=2))