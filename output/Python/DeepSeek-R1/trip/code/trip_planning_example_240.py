import json

def calculate_itinerary():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Prague"},  # 2 days including flight day
        {"day_range": "Day 2-6", "place": "Stockholm"},  # 5 days including flight days
        {"day_range": "Day 6-8", "place": "Berlin"},  # 3 days including flight day
        {"day_range": "Day 8-12", "place": "Tallinn"}  # 5 days including flight day
    ]
    
    # Verify direct flight connections between consecutive cities
    connections = [
        ("Prague", "Stockholm"),
        ("Stockholm", "Berlin"),
        ("Berlin", "Tallinn")
    ]
    valid_flights = {
        ('Berlin', 'Tallinn'), ('Prague', 'Tallinn'), ('Stockholm', 'Tallinn'),
        ('Prague', 'Stockholm'), ('Stockholm', 'Berlin')
    }
    
    for i in range(1, len(itinerary)):
        prev = itinerary[i-1]['place']
        curr = itinerary[i]['place']
        if (prev, curr) not in valid_flights and (curr, prev) not in valid_flights:
            raise ValueError(f"No direct flight between {prev} and {curr}")
    
    return {"itinerary": itinerary}

print(json.dumps(calculate_itinerary(), indent=2))