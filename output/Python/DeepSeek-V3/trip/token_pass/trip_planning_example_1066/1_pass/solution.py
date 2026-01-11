import itertools
import json

def main():
    # City stay durations
    durations = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 2,
        "Helsinki": 5,
        "Split": 3,
        "London": 5
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Helsinki", "London"),
        ("Split", "Madrid"),
        ("Helsinki", "Madrid"),
        ("London", "Madrid"),
        ("Brussels", "London"),
        ("Bucharest", "London"),
        ("Brussels", "Bucharest"),
        ("Bucharest", "Madrid"),
        ("Split", "Helsinki"),
        ("Mykonos", "Madrid"),
        ("Stuttgart", "London"),
        ("Helsinki", "Brussels"),
        ("Brussels", "Madrid"),
        ("Split", "London"),
        ("Stuttgart", "Split"),
        ("London", "Mykonos")
    ]
    
    # Make lookup set for faster check
    flight_set = set()
    for a, b in direct_flights:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    cities = list(durations.keys())
    
    # We'll search over permutations
    for perm in itertools.permutations(cities):
        # Check Madrid is last city (since days 20-21 are Madrid)
        if perm[-1] != "Madrid":
            continue
        
        # Check consecutive cities have direct flights
        valid_flight = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in flight_set:
                valid_flight = False
                break
        if not valid_flight:
            continue
        
        # Check Stuttgart in first 4 days
        # Compute day ranges
        day = 1
        stuttgart_within_first_4 = False
        for city in perm:
            dur = durations[city]
            if city == "Stuttgart":
                if day <= 4:
                    stuttgart_within_first_4 = True
            day += dur
        if not stuttgart_within_first_4:
            continue
        
        # Check total days = 21
        total_days = sum(durations[city] for city in perm)
        if total_days != 21:
            continue
        
        # All constraints satisfied, build itinerary
        itinerary = []
        day_start = 1
        for city in perm:
            dur = durations[city]
            day_end = day_start + dur - 1
            if day_start == day_end:
                day_range_str = f"Day {day_start}"
            else:
                day_range_str = f"Day {day_start}-{day_end}"
            itinerary.append({
                "day_range": day_range_str,
                "place": city
            })
            day_start += dur
        
        # Output result
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
        return
    
    # If no valid plan found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()