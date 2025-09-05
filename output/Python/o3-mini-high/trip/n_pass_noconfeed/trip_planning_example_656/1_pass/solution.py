import itertools
import json

def main():
    # Trip parameters
    total_trip_days = 19
    city_durations = {
        "Reykjavik": 5,
        "Istanbul": 4,
        "Edinburgh": 5,
        "Oslo": 2,
        "Stuttgart": 3,
        "Bucharest": 5,
    }
    
    # Allowed flights.
    # For each undirected connection, we add both directions.
    # Note: The flight from Reykjavik to Stuttgart is directional.
    allowed_flights = set()
    # Bucharest and Oslo (both ways)
    allowed_flights.add(("Bucharest", "Oslo"))
    allowed_flights.add(("Oslo", "Bucharest"))
    # Istanbul and Oslo (both ways)
    allowed_flights.add(("Istanbul", "Oslo"))
    allowed_flights.add(("Oslo", "Istanbul"))
    # Reykjavik -> Stuttgart (only this direction)
    allowed_flights.add(("Reykjavik", "Stuttgart"))
    # Bucharest and Istanbul (both ways)
    allowed_flights.add(("Bucharest", "Istanbul"))
    allowed_flights.add(("Istanbul", "Bucharest"))
    # Stuttgart and Edinburgh (both ways)
    allowed_flights.add(("Stuttgart", "Edinburgh"))
    allowed_flights.add(("Edinburgh", "Stuttgart"))
    # Istanbul and Edinburgh (both ways)
    allowed_flights.add(("Istanbul", "Edinburgh"))
    allowed_flights.add(("Edinburgh", "Istanbul"))
    # Oslo and Reykjavik (both ways)
    allowed_flights.add(("Oslo", "Reykjavik"))
    allowed_flights.add(("Reykjavik", "Oslo"))
    # Istanbul and Stuttgart (both ways)
    allowed_flights.add(("Istanbul", "Stuttgart"))
    allowed_flights.add(("Stuttgart", "Istanbul"))
    # Oslo and Edinburgh (both ways)
    allowed_flights.add(("Oslo", "Edinburgh"))
    allowed_flights.add(("Edinburgh", "Oslo"))
    
    # List of cities
    cities = list(city_durations.keys())
    
    valid_itinerary = None
    valid_timeline = None
    
    # For each permutation of cities, check if the flight connections work
    for order in itertools.permutations(cities):
        # Istanbul and Oslo shouldn't be the first city because of their respective time-window constraints.
        if order[0] in ["Istanbul", "Oslo"]:
            continue

        # Check flight connectivity for consecutive cities.
        flight_ok = True
        for i in range(len(order) - 1):
            dep = order[i]
            arr = order[i+1]
            # Check if the flight from dep to arr is allowed.
            if (dep, arr) not in allowed_flights:
                flight_ok = False
                break
        if not flight_ok:
            continue
        
        # Compute day ranges for each city.
        # The rule: first city: days 1 to duration; for each subsequent city,
        # arrival day equals the previous city's end day.
        timeline = []
        day = 1
        for city in order:
            start_day = day
            end_day = start_day + city_durations[city] - 1
            timeline.append((start_day, end_day))
            # The departure flight occurs on the end_day, which is also the arrival day of the next city.
            day = end_day
        
        # The overall trip should be exactly total_trip_days.
        if day != total_trip_days:
            continue
        
        # Check Istanbul meeting friends window: must be in Istanbul on some day between Day 5 and Day 8.
        # That is, Istanbul's time window [start, end] must intersect [5,8] (inclusive).
        meets_constraints = True
        for city, (start, end) in zip(order, timeline):
            if city == "Istanbul":
                if not (start <= 8 and end >= 5):
                    meets_constraints = False
                    break
            if city == "Oslo":
                # Must visit relatives in Oslo between day 8 and 9.
                if not (start <= 9 and end >= 8):
                    meets_constraints = False
                    break
        if not meets_constraints:
            continue

        # Found a valid itinerary satisfying all constraints.
        valid_itinerary = order
        valid_timeline = timeline
        break

    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        # Build the itinerary output as a list of dictionaries.
        itinerary_output = []
        for city, (start, end) in zip(valid_itinerary, valid_timeline):
            day_range = f"Day {start}-{end}"
            itinerary_output.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_output}

    # Output the result as JSON.
    print(json.dumps(result))

if __name__ == "__main__":
    main()