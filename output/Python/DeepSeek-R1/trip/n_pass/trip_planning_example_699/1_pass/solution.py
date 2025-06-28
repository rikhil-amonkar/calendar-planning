import json

def main():
    total_days = 16
    cities = {
        "Hamburg": 2,
        "Dublin": 5,
        "Helsinki": 4,
        "Reykjavik": 2,
        "London": 5,
        "Mykonos": 3
    }
    
    fixed_events = [
        {"city": "Dublin", "start": 2, "end": 6},
        {"city": "Hamburg", "start": 1, "end": 2}
    ]
    wedding_event = {"city": "Reykjavik", "start": 9, "end": 10}
    
    flight_pairs = [
        ("Dublin", "London"),
        ("Hamburg", "Dublin"),
        ("Helsinki", "Reykjavik"),
        ("Hamburg", "London"),
        ("Dublin", "Helsinki"),
        ("Reykjavik", "London"),
        ("London", "Mykonos"),
        ("Dublin", "Reykjavik"),
        ("Hamburg", "Helsinki"),
        ("Helsinki", "London")
    ]
    
    direct_flights = set()
    for a, b in flight_pairs:
        direct_flights.add((a, b))
        direct_flights.add((b, a))
    
    order = ["Hamburg", "Dublin", "Helsinki", "Reykjavik", "London", "Mykonos"]
    
    current_day = 1
    itinerary = []
    segments = {}
    
    for city in order:
        duration = cities[city]
        end_day = current_day + duration - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        segments[city] = (current_day, end_day)
        current_day = end_day
    
    if current_day != total_days:
        raise RuntimeError(f"Total days mismatch: expected {total_days}, got {current_day}")
    
    for event in fixed_events:
        city = event["city"]
        req_start = event["start"]
        req_end = event["end"]
        actual_start, actual_end = segments[city]
        if actual_start > req_start or actual_end < req_end:
            raise RuntimeError(f"Event constraint failed for {city}")
    
    wedding_city = wedding_event["city"]
    wed_start = wedding_event["start"]
    wed_end = wedding_event["end"]
    actual_start, actual_end = segments[wedding_city]
    if actual_end < wed_start or actual_start > wed_end:
        raise RuntimeError("Wedding event constraint failed")
    
    for i in range(len(order) - 1):
        city_from = order[i]
        city_to = order[i+1]
        if (city_from, city_to) not in direct_flights:
            raise RuntimeError(f"No direct flight from {city_from} to {city_to}")
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()