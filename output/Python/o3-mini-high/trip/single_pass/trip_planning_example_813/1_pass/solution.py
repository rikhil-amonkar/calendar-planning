#!/usr/bin/env python3
import itertools
import json

def main():
    # Constraints: durations for each city (in days)
    durations = {
        "Seville": 5,
        "Vilnius": 3,
        "Santorini": 2,
        "London": 2,
        "Stuttgart": 3,
        "Dublin": 3,
        "Frankfurt": 5
    }
    
    # Allowed direct flights (bidirectional)
    flight_map = {
        "Frankfurt": ["Dublin", "London", "Stuttgart", "Vilnius"],
        "Dublin": ["Frankfurt", "London", "Seville", "Santorini"],
        "London": ["Frankfurt", "Dublin", "Santorini", "Stuttgart"],
        "Seville": ["Dublin"],
        "Santorini": ["London", "Dublin"],
        "Stuttgart": ["Frankfurt", "London"],
        "Vilnius": ["Frankfurt"]
    }
    
    # Special scheduling constraints:
    # - Meet friends in London between day 9 and day 10 (London's visit must cover at least one of these days)
    # - Visit relatives in Stuttgart between day 7 and day 9 (Stuttgart's visit must cover at least one of these days)
    
    # The total distinct days of the trip will be:
    # sum(durations) - (# transitions).
    # With 7 cities and 6 flights (each flight day counts in both cities),
    # total distinct days = (5+3+2+2+3+3+5) - 6 = 23 - 6 = 17.
    
    cities = list(durations.keys())
    valid_itinerary = None

    # Search through all permutations of the cities to find an ordering that:
    # 1. Uses available direct flights between consecutive cities.
    # 2. Satisfies the London and Stuttgart day-window constraints.
    for perm in itertools.permutations(cities):
        # Check flight connectivity between consecutive cities.
        valid_flights = True
        for i in range(len(perm) - 1):
            a = perm[i]
            b = perm[i+1]
            if b not in flight_map.get(a, []) and a not in flight_map.get(b, []):
                valid_flights = False
                break
        if not valid_flights:
            continue
        
        # Build the itinerary with overlapping flight days.
        # Rule: the first city occupies days 1 to (duration),
        # and each subsequent city starts on the same day the previous city ended.
        itinerary = []
        current_day = 1
        for city in perm:
            start_day = current_day
            end_day = start_day + durations[city] - 1
            itinerary.append((city, start_day, end_day))
            # On the flight day (end_day) the person is in both cities.
            current_day = end_day
        
        # Confirm total distinct days equals 17.
        if current_day != 17:
            continue
        
        # Find London and Stuttgart segments.
        london_segment = next((seg for seg in itinerary if seg[0] == "London"), None)
        stuttgart_segment = next((seg for seg in itinerary if seg[0] == "Stuttgart"), None)
        if not london_segment or not stuttgart_segment:
            continue
        
        # Check if London's days include either day 9 or day 10.
        london_days = set(range(london_segment[1], london_segment[2] + 1))
        if not london_days.intersection({9, 10}):
            continue
        
        # Check if Stuttgart's days include a day between day 7 and day 9.
        stuttgart_days = set(range(stuttgart_segment[1], stuttgart_segment[2] + 1))
        if not stuttgart_days.intersection({7, 8, 9}):
            continue
        
        # We found an itinerary that meets all criteria.
        valid_itinerary = itinerary
        break

    # Build the JSON output.
    output = {"itinerary": []}
    if valid_itinerary:
        for city, start_day, end_day in valid_itinerary:
            output["itinerary"].append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })

    print(json.dumps(output))

if __name__ == "__main__":
    main()