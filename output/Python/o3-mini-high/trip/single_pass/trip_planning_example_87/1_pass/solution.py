#!/usr/bin/env python3
import json
from itertools import permutations

def main():
    # Input variables: trip constraints
    total_days = 7
    # Required days in each city
    city_stays = {
        "Riga": 2,
        "Amsterdam": 2,
        "Mykonos": 5
    }
    # Direct flight connections (assumed bidirectional)
    flight_connections = {
        ("Amsterdam", "Mykonos"),
        ("Mykonos", "Amsterdam"),
        ("Riga", "Amsterdam"),
        ("Amsterdam", "Riga")
    }
    # Constraint: visit relatives in Riga between day 1 and day 2, so start must be Riga.
    start_city = "Riga"
    
    valid_itinerary = None
    # Find valid ordering among the cities that satisfies:
    # 1. Starting in Riga.
    # 2. Each consecutive city is connected by a direct flight.
    # 3. The overall calendar days match the calculation:
    #    total calendar days = sum(required days) - (#transitions) where each flight day counts for both cities.
    for perm in permutations(city_stays.keys()):
        if perm[0] != start_city:
            continue
        direct = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in flight_connections:
                direct = False
                break
        if not direct:
            continue
        # Check if the overlapping flight days subtract exactly to give total_days.
        # Number of transitions = len(perm) - 1.
        if sum(city_stays[city] for city in perm) - (len(perm) - 1) == total_days:
            valid_itinerary = perm
            break

    itinerary_result = {"itinerary": []}
    
    # If a valid itinerary is found, determine the day ranges.
    # Rule: if flying from city A to city B on day X then day X counts as both A and B.
    # Thus, we set the segment for the first city from day 1 to day (1 + required - 1).
    # For subsequent segments, the starting day is the previous segment's end (the flight day).
    if valid_itinerary:
        segments = []
        current_day = 1
        for city in valid_itinerary:
            required = city_stays[city]
            segment_end = current_day + required - 1
            segments.append({
                "day_range": f"Day {current_day}-{segment_end}",
                "place": city
            })
            # Next city starts on the same day as this segment's end (flight day overlap)
            current_day = segment_end
        itinerary_result["itinerary"] = segments

    print(json.dumps(itinerary_result))

if __name__ == '__main__':
    main()