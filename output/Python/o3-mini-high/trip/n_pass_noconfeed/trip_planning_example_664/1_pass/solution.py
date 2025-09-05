#!/usr/bin/env python3
import itertools
import json

def main():
    # Total trip days and required stay durations (these include the flight overlap)
    total_days = 18
    durations = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2,
    }
    
    # Special time-window constraints:
    # For each city, its visit must include at least one day within the given window.
    special_windows = {
        "Bucharest": (1, 4),   # Must visit relatives in Bucharest between day 1 and day 4
        "Munich": (4, 8),      # Must attend the wedding in Munich between day 4 and day 8
        "Seville": (8, 12),    # Must meet friends in Seville between day 8 and day 12
    }
    
    # List of direct flight connections given (bidirectional)
    direct_flights = [
        ("Milan", "Stockholm"),
        ("Munich", "Stockholm"),
        ("Bucharest", "Munich"),
        ("Munich", "Seville"),
        ("Stockholm", "Tallinn"),
        ("Munich", "Milan"),
        ("Munich", "Tallinn"),
        ("Seville", "Milan")
    ]
    
    # Build a set of flight connections that works in both directions.
    flights = set()
    for city_a, city_b in direct_flights:
        flights.add((city_a, city_b))
        flights.add((city_b, city_a))
    
    # List the cities (order not pre-determined).
    # Our input parameters allow us to choose an ordering that satisfies both connectivity 
    # and the time-window constraints.
    cities = ["Bucharest", "Munich", "Seville", "Milan", "Stockholm", "Tallinn"]
    
    valid_itinerary = None
    
    # Search over all possible orderings of the cities.
    for perm in itertools.permutations(cities):
        # Check if each consecutive leg has a direct flight.
        valid_route = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in flights:
                valid_route = False
                break
        if not valid_route:
            continue

        # Compute the day intervals for each city.
        # The rule is: the first city covers days [1, duration],
        # and each subsequent city starts on the last day of the previous city.
        segments = []
        current_day = 1
        for city in perm:
            start_day = current_day
            end_day = start_day + durations[city] - 1
            segments.append((city, start_day, end_day))
            current_day = end_day  # departure day overlaps with arrival day
        if current_day != total_days:
            continue
        
        # Check the special time-window constraints.
        meets_windows = True
        for city, seg_start, seg_end in segments:
            if city in special_windows:
                win_start, win_end = special_windows[city]
                # There must be an overlap between the city's visit and the required window.
                if seg_end < win_start or seg_start > win_end:
                    meets_windows = False
                    break
        if not meets_windows:
            continue

        # If everything is satisfied, this itinerary is acceptable.
        valid_itinerary = segments
        break

    # Build the JSON output in the required format.
    output = {"itinerary": []}
    if valid_itinerary is not None:
        for city, seg_start, seg_end in valid_itinerary:
            output["itinerary"].append({
                "day_range": f"Day {seg_start}-{seg_end}",
                "place": city
            })
    print(json.dumps(output, indent=4))

if __name__ == "__main__":
    main()