#!/usr/bin/env python3
import json
import itertools

def main():
    # Define cities with required durations and event constraints.
    # Each city has a "duration" value.
    # Cities with events also include a tuple representing the event’s time window.
    cities_info = {
        "Porto": {"duration": 2},
        "Geneva": {"duration": 3},
        "Mykonos": {"duration": 3, "friend_meeting": (10, 12)},  # Must meet friend on one day between day 10 and 12
        "Manchester": {"duration": 4, "wedding": (15, 18)},       # Wedding to attend between day 15 and 18
        "Hamburg": {"duration": 5},
        "Naples": {"duration": 5},
        "Frankfurt": {"duration": 2, "show": (5, 6)}              # Annual show from day 5 to day 6
    }
    
    cities = list(cities_info.keys())
    
    # Define allowed direct flights as directed edges.
    flights = set()
    # Helper to add symmetric (bidirectional) flights.
    def add_symmetric(a, b):
        flights.add((a, b))
        flights.add((b, a))
    
    add_symmetric("Hamburg", "Frankfurt")
    add_symmetric("Naples", "Mykonos")
    add_symmetric("Hamburg", "Porto")
    # "from Hamburg to Geneva" is only available in this direction.
    flights.add(("Hamburg", "Geneva"))
    add_symmetric("Mykonos", "Geneva")
    add_symmetric("Frankfurt", "Geneva")
    add_symmetric("Frankfurt", "Porto")
    add_symmetric("Geneva", "Porto")
    add_symmetric("Geneva", "Manchester")
    add_symmetric("Naples", "Manchester")
    add_symmetric("Frankfurt", "Naples")
    add_symmetric("Frankfurt", "Manchester")
    add_symmetric("Naples", "Geneva")
    add_symmetric("Porto", "Manchester")
    add_symmetric("Hamburg", "Manchester")
    
    valid_itinerary = None

    # We use permutation search over the 7 cities.
    # For a given ordering, we compute the overlapping day schedule.
    # Rule: The first city starts on day 1.
    # For each subsequent city, the start day equals the previous city's end day 
    # (since if you fly on day X, you are in both cities on day X).
    for perm in itertools.permutations(cities):
        intervals = []
        current_day = 1
        valid = True
        
        # Compute each city’s start and end days.
        for city in perm:
            duration = cities_info[city]["duration"]
            start_day = current_day
            end_day = start_day + duration - 1
            intervals.append((start_day, end_day))
            current_day = end_day  # Overlap: next city starts on the same day this one ends.
        
        # The total trip must end on day 18.
        if intervals[-1][1] != 18:
            valid = False
        
        # Check event constraints for cities that have specific requirements.
        for city, (start_day, end_day) in zip(perm, intervals):
            info = cities_info[city]
            # Frankfurt must cover the annual show on day 5 and 6.
            if city == "Frankfurt":
                # With a duration of 2, the only valid interval is exactly day 5 to day 6.
                if start_day != 5 or end_day != 6:
                    valid = False
                    break
            # Mykonos must have at least one day between day 10 and day 12.
            if city == "Mykonos" and "friend_meeting" in info:
                fm_start, fm_end = info["friend_meeting"]
                # Check for intersection between [start_day, end_day] and [fm_start, fm_end]
                if end_day < fm_start or start_day > fm_end:
                    valid = False
                    break
            # Manchester must include a day between day 15 and day 18 for the wedding.
            if city == "Manchester" and "wedding" in info:
                w_start, w_end = info["wedding"]
                if end_day < w_start or start_day > w_end:
                    valid = False
                    break
        
        if not valid:
            continue

        # Check that each flight from one city to the next is directly connected.
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in flights:
                valid = False
                break
        if not valid:
            continue

        # If we reached here, we have found a valid itinerary.
        valid_itinerary = []
        for city, (start_day, end_day) in zip(perm, intervals):
            valid_itinerary.append({
                "day_range": "Day {}-{}".format(start_day, end_day),
                "place": city
            })
        break

    if valid_itinerary is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": valid_itinerary}

    # Output the result as a JSON-formatted dictionary.
    print(json.dumps(output))

if __name__ == "__main__":
    main()