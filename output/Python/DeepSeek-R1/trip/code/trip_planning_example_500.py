import json

def main():
    itinerary = []
    # Hamburg: 7 days (days 1-7, departure on day 7)
    itinerary.append({"day_range": "Day 1-7", "place": "Hamburg"})
    # Split: 7 days (days 7-13, departure on day 13)
    itinerary.append({"day_range": "Day 7-13", "place": "Split"})
    # Lyon: 2 days (days 13-14, departure on day 14)
    itinerary.append({"day_range": "Day 13-14", "place": "Lyon"})
    # Munich: 6 days (days 14-19, departure on day 19)
    itinerary.append({"day_range": "Day 14-19", "place": "Munich"})
    # Manchester: 2 days (days 19-20)
    itinerary.append({"day_range": "Day 19-20", "place": "Manchester"})
    
    # Validate flight connections
    flight_routes = {
        'Hamburg': ['Manchester', 'Munich', 'Split'],
        'Split': ['Hamburg', 'Munich', 'Lyon'],
        'Lyon': ['Split', 'Munich'],
        'Munich': ['Manchester', 'Hamburg', 'Split', 'Lyon'],
        'Manchester': ['Hamburg', 'Munich', 'Split']
    }
    prev_city = None
    for entry in itinerary:
        current_city = entry['place']
        if prev_city and current_city not in flight_routes.get(prev_city, []):
            raise ValueError(f"No flight from {prev_city} to {current_city}")
        prev_city = current_city
    
    # Validate day counts
    required_days = {
        'Hamburg': 7,
        'Munich': 6,
        'Manchester': 2,
        'Lyon': 2,
        'Split': 7
    }
    for entry in itinerary:
        days = entry['day_range']
        start, end = map(int, days.split()[1].split('-'))
        city = entry['place']
        required_days[city] -= (end - start + 1)
    if any(required_days.values()):
        raise ValueError("Day count mismatch")
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()