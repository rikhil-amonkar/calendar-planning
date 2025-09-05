#!/usr/bin/env python3
import itertools
import json

def main():
    # Trip constraints and durations
    total_days = 15
    city_durations = {
        "Stuttgart": 5,    # Must include workshop between day 11 and day 15
        "Manchester": 7,   # Must include wedding between day 1 and day 7
        "Madrid": 4,
        "Vienna": 2
    }
    
    # Wedding must be attended in Manchester between day 1 and day 7
    wedding_range = (1, 7)
    # Workshop must be attended in Stuttgart between day 11 and day 15
    workshop_range = (11, 15)
    
    # Direct flights available (undirected edges)
    allowed_flights = {
        frozenset(["Vienna", "Stuttgart"]),
        frozenset(["Manchester", "Vienna"]),
        frozenset(["Madrid", "Vienna"]),
        frozenset(["Manchester", "Stuttgart"]),
        frozenset(["Manchester", "Madrid"])
    }
    
    cities = list(city_durations.keys())
    valid_itinerary = None

    # We try all orderings of the cities.
    for perm in itertools.permutations(cities):
        schedule = []
        start = 1
        # Build schedule based on overlapping flight days.
        # If a flight happens on day X, then day X counts both for the city we're leaving and the city we're arriving.
        for city in perm:
            duration = city_durations[city]
            end = start + duration - 1
            schedule.append((city, start, end))
            # Next city starts on the same day as the previous city ended (flight day overlap)
            start = end  
        
        # Check that overall itinerary spans exactly total_days
        if schedule[-1][2] != total_days:
            continue
        
        # Check connectivity: each consecutive pair must have a direct flight.
        connectivity_ok = True
        for i in range(len(schedule) - 1):
            city_from = schedule[i][0]
            city_to = schedule[i + 1][0]
            if frozenset([city_from, city_to]) not in allowed_flights:
                connectivity_ok = False
                break
        if not connectivity_ok:
            continue
        
        # Check wedding constraint for Manchester:
        # The Manchester visit interval must include at least one day between day 1 and 7.
        wedding_ok = True
        for city, s, e in schedule:
            if city == "Manchester":
                if s > wedding_range[1]:
                    wedding_ok = False
                break
        if not wedding_ok:
            continue
        
        # Check workshop constraint for Stuttgart:
        # Stuttgart visit interval must include at least one day between day 11 and 15.
        workshop_ok = True
        for city, s, e in schedule:
            if city == "Stuttgart":
                if e < workshop_range[0]:
                    workshop_ok = False
                break
        if not workshop_ok:
            continue
        
        # If all constraints are met, select this itinerary.
        valid_itinerary = schedule
        break

    # Format the itinerary output as the required JSON structure.
    result = {"itinerary": []}
    if valid_itinerary is not None:
        for city, s, e in valid_itinerary:
            result["itinerary"].append({
                "day_range": f"Day {s}-{e}",
                "place": city
            })
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()