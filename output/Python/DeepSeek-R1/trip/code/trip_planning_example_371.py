import json

def calculate_itinerary():
    cities = {
        'Vienna': 2,
        'Stockholm': 5,
        'Split': 3,
        'Nice': 2
    }
    direct_flights = {
        'Vienna': ['Stockholm', 'Nice', 'Split'],
        'Stockholm': ['Vienna', 'Split', 'Nice'],
        'Nice': ['Vienna', 'Stockholm'],
        'Split': ['Vienna', 'Stockholm']
    }

    itinerary = [
        {"day_range": "Day 1-2", "place": "Vienna"},
        {"day_range": "Day 3-7", "place": "Stockholm"},
        {"day_range": "Day 5-6", "place": "Nice"},
        {"day_range": "Day 7-9", "place": "Split"}
    ]

    # Validation checks
    days_count = {city: 0 for city in cities}
    for entry in itinerary:
        days = entry['day_range']
        start = int(days.split('-')[0].split()[1])
        end = int(days.split('-')[1]) if '-' in days else start
        duration = end - start + 1
        days_count[entry['place']] += duration

    valid = all(days_count[city] == cities[city] for city in cities)
    prev_place = None
    for entry in itinerary:
        current_place = entry['place']
        if prev_place is not None and prev_place != current_place:
            if current_place not in direct_flights[prev_place]:
                valid = False
                break
        prev_place = current_place

    split_days = [entry for entry in itinerary if entry['place'] == 'Split']
    if len(split_days) != 1 or split_days[0]['day_range'] != "Day 7-9":
        valid = False

    vienna_days = [entry for entry in itinerary if entry['place'] == 'Vienna']
    if len(vienna_days) != 1 or vienna_days[0]['day_range'] != "Day 1-2":
        valid = False

    if valid:
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = calculate_itinerary()
print(json.dumps(result))