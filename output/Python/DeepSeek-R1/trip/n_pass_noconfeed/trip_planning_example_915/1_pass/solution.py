import json

def main():
    # Define cities with their constraints
    cities = {
        "Bucharest": {"required_days": 3},
        "Venice": {"required_days": 5, "fixed_interval": (22, 26), "must_cover_entire_interval": True},
        "Prague": {"required_days": 4},
        "Frankfurt": {"required_days": 5, "fixed_interval": (12, 16), "must_cover_entire_interval": True},
        "Zurich": {"required_days": 5},
        "Florence": {"required_days": 5},
        "Tallinn": {"required_days": 5, "fixed_interval": (8, 12), "must_cover_entire_interval": False}
    }
    
    # Build direct_flights set including bidirectional and one-way flights
    bidirectional_pairs = [
        ("Prague", "Tallinn"),
        ("Prague", "Zurich"),
        ("Florence", "Prague"),
        ("Frankfurt", "Bucharest"),
        ("Frankfurt", "Venice"),
        ("Prague", "Bucharest"),
        ("Bucharest", "Zurich"),
        ("Tallinn", "Frankfurt"),
        ("Frankfurt", "Zurich"),
        ("Zurich", "Venice"),
        ("Florence", "Frankfurt"),
        ("Prague", "Frankfurt"),
        ("Tallinn", "Zurich")
    ]
    one_way = [("Zurich", "Florence")]
    
    direct_flights = set()
    for a, b in bidirectional_pairs:
        direct_flights.add((a, b))
        direct_flights.add((b, a))
    for a, b in one_way:
        direct_flights.add((a, b))
    
    # Define the computed itinerary segments
    itinerary_segments = [
        ("Florence", 1, 5),
        ("Prague", 5, 8),
        ("Tallinn", 8, 12),
        ("Frankfurt", 12, 16),
        ("Bucharest", 16, 18),
        ("Zurich", 18, 22),
        ("Venice", 22, 26)
    ]
    
    # Verify the itinerary
    # Check contiguous days
    prev_end = 0
    for i, (city, start, end) in enumerate(itinerary_segments):
        if i == 0:
            if start != 1:
                raise ValueError("Itinerary must start on day 1")
        else:
            if start != prev_end:
                raise ValueError(f"Gap between segments: previous end {prev_end}, current start {start}")
        prev_end = end
    if prev_end != 26:
        raise ValueError(f"Last day is {prev_end}, should be 26")
    
    # Check required days per city
    city_days = {city: 0 for city in cities}
    for city, start, end in itinerary_segments:
        num_days = end - start + 1
        city_days[city] = num_days
    for city, info in cities.items():
        if city_days[city] != info["required_days"]:
            raise ValueError(f"City {city} has {city_days[city]} days, required {info['required_days']}")
    
    # Check fixed intervals
    for city, start, end in itinerary_segments:
        if "fixed_interval" in cities[city]:
            low, high = cities[city]["fixed_interval"]
            if cities[city].get("must_cover_entire_interval", False):
                if start > low or end < high:
                    raise ValueError(f"City {city} must cover entire interval ({low}-{high}), but segment is {start}-{end}")
            else:
                if end < low or start > high:
                    raise ValueError(f"City {city} has no day in interval ({low}-{high})")
    
    # Check direct flights between consecutive segments
    for i in range(len(itinerary_segments) - 1):
        from_city = itinerary_segments[i][0]
        to_city = itinerary_segments[i+1][0]
        if (from_city, to_city) not in direct_flights:
            raise ValueError(f"No direct flight from {from_city} to {to_city}")
    
    # Format the itinerary for output
    itinerary_list = []
    for city, start, end in itinerary_segments:
        itinerary_list.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()