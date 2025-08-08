#!/usr/bin/env python3
import itertools
import json

def main():
    # Input variables for trip constraints
    total_trip_days = 18
    # Define the cities and their required durations.
    # Note: The sum of durations is 23, and with 5 flight transitions overlapping,
    # the distinct total days become 23 - 5 = 18.
    durations = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4
    }
    cities = list(durations.keys())
    
    # Define direct flight connections (bidirectional)
    direct_flights = [
        ("Helsinki", "Prague"),
        ("Prague", "Valencia"),
        ("Valencia", "Porto"),
        ("Helsinki", "Reykjavik"),
        ("Dubrovnik", "Helsinki"),
        ("Reykjavik", "Prague")
    ]
    # Build a set of allowed flight pairs in both directions.
    flights_set = set()
    for a, b in direct_flights:
        flights_set.add((a, b))
        flights_set.add((b, a))
    
    # Constraint: Meet friend in Porto between day 16 and day 18.
    meeting_city = "Porto"
    meeting_start, meeting_end = 16, 18
    
    # We require an itinerary that visits each city exactly once
    # with allowed direct flights between consecutive cities.
    # Also note that Dubrovnik and Porto have degree one, so they must be endpoints.
    valid_itinerary = None
    for order in itertools.permutations(cities):
        # For the underlying flight graph, Dubrovnik and Porto (degree1) must be endpoints.
        if order[0] != "Dubrovnik" or order[-1] != "Porto":
            continue
        # Check every consecutive flight is allowed.
        valid_route = True
        for i in range(len(order) - 1):
            if (order[i], order[i+1]) not in flights_set:
                valid_route = False
                break
        if not valid_route:
            continue
        
        # Compute day assignments.
        itinerary_plan = []
        current_day = 1
        # Keep track of the day range for each city for later check.
        city_day_ranges = {}
        for city in order:
            start_day = current_day
            end_day = start_day + durations[city] - 1
            itinerary_plan.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
            city_day_ranges[city] = (start_day, end_day)
            # Next city begins on the same day as the flight day (overlap)
            current_day = end_day
        
        # After visiting all cities, total distinct days should be total_trip_days.
        if current_day != total_trip_days:
            continue
        
        # Check the meeting constraint: Porto's day range must include at least one day between 16 and 18.
        porto_start, porto_end = city_day_ranges.get(meeting_city, (0, 0))
        # Condition: Porto interval and meeting interval must overlap.
        if porto_end >= meeting_start and porto_start <= meeting_end:
            valid_itinerary = itinerary_plan
            break

    # If no valid itinerary is found, return an empty itinerary.
    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": valid_itinerary}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()