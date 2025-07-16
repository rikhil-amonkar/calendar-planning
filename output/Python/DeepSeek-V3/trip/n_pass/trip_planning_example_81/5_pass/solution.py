import json

def plan_trip():
    # Flight connections
    connections = {
        'Budapest': ['Mykonos', 'Hamburg'],
        'Mykonos': ['Budapest'],
        'Hamburg': ['Budapest']
    }
    
    itinerary = [
        {"day_range": "Day 1-3", "place": "Budapest", "activity": "Explore the city"},
        {"day_range": "Day 4", "place": "Mykonos", "activity": "Attend conference"},
        {"day_range": "Day 5-6", "place": "Budapest", "activity": "Sightseeing"},
        {"day_range": "Day 7-8", "place": "Hamburg", "activity": "Visit friends"},
        {"day_range": "Day 9", "place": "Budapest", "activity": "Return home"}
    ]
    
    # Validate connections
    for i in range(1, len(itinerary)):
        current = itinerary[i]['place']
        previous = itinerary[i-1]['place']
        if current not in connections.get(previous, []):
            raise ValueError(f"No flight connection from {previous} to {current}")
    
    return {"itinerary": itinerary}

result = plan_trip()
print(json.dumps(result, indent=2))