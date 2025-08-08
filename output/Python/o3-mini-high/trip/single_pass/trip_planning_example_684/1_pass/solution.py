#!/usr/bin/env python3
import itertools
import json

def main():
    # Input variables
    total_days = 23
    city_durations = {
        "Amsterdam": 4,
        "Edinburgh": 5,
        "Brussels": 5,
        "Vienna": 5,
        "Berlin": 4,
        "Reykjavik": 5
    }
    # Time window constraints (inclusive)
    # Amsterdam: must visit relatives between day 5 and day 8
    amsterdam_window = (5, 8)
    # Berlin: must meet a friend between day 16 and day 19
    berlin_window = (16, 19)
    # Reykjavik: must attend workshop between day 12 and day 16
    reykjavik_window = (12, 16)
    
    # Flight connections (bidirectional direct flights)
    flight_graph = {
        "Amsterdam": {"Berlin", "Edinburgh", "Reykjavik", "Vienna"},
        "Edinburgh": {"Berlin", "Amsterdam", "Brussels"},
        "Berlin": {"Amsterdam", "Edinburgh", "Vienna", "Brussels", "Reykjavik"},
        "Vienna": {"Berlin", "Reykjavik", "Brussels", "Amsterdam"},
        "Brussels": {"Berlin", "Edinburgh", "Vienna", "Reykjavik"},
        "Reykjavik": {"Vienna", "Brussels", "Amsterdam", "Berlin"}
    }
    
    cities = list(city_durations.keys())
    valid_itinerary = None

    # Iterate over all permutations of cities
    for perm in itertools.permutations(cities):
        # Check that every consecutive flight is a valid direct connection
        valid_path = True
        for i in range(len(perm)-1):
            if perm[i+1] not in flight_graph[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue

        # Compute itinerary timeline using overlapping flight days.
        # The rule: first city's start day is 1. For every subsequent city,
        # its start day equals the previous city's end day (flight day overlap).
        itinerary_schedule = []
        current_day = 1
        for city in perm:
            duration = city_durations[city]
            start_day = current_day
            end_day = start_day + duration - 1
            itinerary_schedule.append((city, start_day, end_day))
            current_day = end_day  # Overlap: next city starts on the same day this city ends

        # Verify the total itinerary fits the planned total days
        if itinerary_schedule[-1][2] != total_days:
            continue

        # Check the specific time window constraints for special cities.
        constraints_ok = True
        for city, start_day, end_day in itinerary_schedule:
            if city == "Amsterdam":
                # Must have some day between 5 and 8
                if not (start_day <= amsterdam_window[1] and end_day >= amsterdam_window[0]):
                    constraints_ok = False
                    break
            if city == "Berlin":
                if not (start_day <= berlin_window[1] and end_day >= berlin_window[0]):
                    constraints_ok = False
                    break
            if city == "Reykjavik":
                if not (start_day <= reykjavik_window[1] and end_day >= reykjavik_window[0]):
                    constraints_ok = False
                    break
        if not constraints_ok:
            continue

        # Found a valid itinerary that satisfies all constraints.
        valid_itinerary = itinerary_schedule
        break

    # Build output JSON following the specified structure.
    output = {}
    itinerary_list = []
    if valid_itinerary is not None:
        for city, start_day, end_day in valid_itinerary:
            itinerary_list.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
    output["itinerary"] = itinerary_list

    print(json.dumps(output))

if __name__ == '__main__':
    main()