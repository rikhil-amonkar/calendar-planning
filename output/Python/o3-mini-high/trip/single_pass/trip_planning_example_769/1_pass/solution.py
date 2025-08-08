#!/usr/bin/env python3
import json
import itertools

def main():
    # Define city durations (in days)
    city_durations = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4
    }
    
    # Define flight connectivity (bidirectional)
    flight_connections = {
        "Porto": {"Amsterdam", "Munich"},
        "Amsterdam": {"Porto", "Munich", "Reykjavik", "Santorini", "Prague"},
        "Munich": {"Amsterdam", "Porto", "Reykjavik", "Prague"},
        "Reykjavik": {"Amsterdam", "Munich", "Prague"},
        "Prague": {"Reykjavik", "Amsterdam", "Munich"},
        "Santorini": {"Amsterdam"}
    }
    
    # Event constraint functions:
    # Wedding in Reykjavik must be between day 4 and day 7 (inclusive)
    def reykjavik_event_valid(start, end):
        # There must be an overlap between [start, end] and [4,7]
        return not (end < 4 or start > 7)
    
    # Friend meeting in Munich must be between day 7 and day 10 (inclusive)
    def munich_event_valid(start, end):
        return not (end < 7 or start > 10)
    
    # Conference in Amsterdam must cover days 14 and 15
    def amsterdam_event_valid(start, end):
        return (start <= 14) and (end >= 15)
    
    valid_itinerary = None

    cities = list(city_durations.keys())
    # There are 6 cities; we must visit all in some order.
    # For each permutation, we assign a timeline with overlapping flight days.
    for perm in itertools.permutations(cities):
        # Check flight connectivity between consecutive cities.
        valid_route = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in flight_connections[perm[i]]:
                valid_route = False
                break
        if not valid_route:
            continue

        # Build itinerary timeline.
        # Rule: The first city is visited for its full duration starting at Day 1.
        # For each subsequent city, the arrival (flight) day is the last day of the previous city.
        itinerary_segments = []
        current_day = 1
        for i, city in enumerate(perm):
            duration = city_durations[city]
            # For the first city: segment = [current_day, current_day + duration - 1]
            # For subsequent cities: same formula since flight day is shared.
            start_day = current_day
            end_day = start_day + duration - 1
            itinerary_segments.append((city, start_day, end_day))
            current_day = end_day  # next city starts on this day (shared overlap)
        
        # The overall itinerary must span exactly 16 unique days.
        if itinerary_segments[-1][2] != 16:
            continue
        
        # Check event constraints.
        # For Reykjavik: wedding between day 4 and 7.
        seg_dict = {city: (start, end) for city, start, end in itinerary_segments}
        if "Reykjavik" in seg_dict:
            start, end = seg_dict["Reykjavik"]
            if not reykjavik_event_valid(start, end):
                continue
        # For Munich: friend meet between day 7 and 10.
        if "Munich" in seg_dict:
            start, end = seg_dict["Munich"]
            if not munich_event_valid(start, end):
                continue
        # For Amsterdam: conference on days 14 and 15.
        if "Amsterdam" in seg_dict:
            start, end = seg_dict["Amsterdam"]
            if not amsterdam_event_valid(start, end):
                continue
        
        # Found a valid itinerary.
        valid_itinerary = itinerary_segments
        break

    # Prepare output with day ranges.
    output = {"itinerary": []}
    if valid_itinerary:
        for city, start, end in valid_itinerary:
            day_range = f"Day {start}-{end}"
            output["itinerary"].append({"day_range": day_range, "place": city})
    print(json.dumps(output))

if __name__ == "__main__":
    main()