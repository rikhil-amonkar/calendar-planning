#!/usr/bin/env python3
import itertools
import json

def main():
    # Trip parameters
    total_days = 20
    # City durations (each duration counts the flight day overlap)
    durations = {
        "Nice": 5,
        "Krakow": 6,
        "Dublin": 7,
        "Lyon": 4,
        "Frankfurt": 2
    }
    # Flight network (bidirectional direct flights)
    flights = {
        "Nice": ["Dublin", "Frankfurt", "Lyon"],
        "Dublin": ["Nice", "Frankfurt", "Krakow", "Lyon"],
        "Krakow": ["Dublin", "Frankfurt"],
        "Lyon": ["Nice", "Frankfurt", "Dublin"],
        "Frankfurt": ["Nice", "Dublin", "Krakow", "Lyon"]
    }
    
    # Fixed constraints:
    # - Must visit Nice between Day 1 and Day 5 (relatives) --> Nice must be first.
    # - Must meet friends in Frankfurt between Day 19 and Day 20 --> Frankfurt must be last.
    fixed_first = "Nice"
    fixed_last = "Frankfurt"
    
    # The remaining cities (order can be computed)
    middle_cities = [city for city in durations if city not in [fixed_first, fixed_last]]
    
    valid_itinerary = None
    # Try all permutations for the middle cities
    for perm in itertools.permutations(middle_cities):
        candidate_order = [fixed_first] + list(perm) + [fixed_last]
        # Check flight connectivity between consecutive cities
        valid_route = True
        for i in range(len(candidate_order) - 1):
            if candidate_order[i+1] not in flights[candidate_order[i]]:
                valid_route = False
                break
        if not valid_route:
            continue
        
        # Compute the itinerary timeline.
        # If flying from A to B on a given day, that day counts for both A and B.
        itinerary = []
        current_day = 1
        for city in candidate_order:
            duration = durations[city]
            end_day = current_day + duration - 1
            itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
            # Next city begins on the same day as the flight day (overlap)
            current_day = end_day
        # Check if the final segment ends exactly on the total trip duration.
        if current_day == total_days:
            valid_itinerary = itinerary
            break

    result = {"itinerary": valid_itinerary if valid_itinerary is not None else []}
    print(json.dumps(result))

if __name__ == "__main__":
    main()