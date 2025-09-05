#!/usr/bin/env python3
import itertools
import json

def main():
    total_days = 17

    # Define the cities and their required effective durations (in days)
    city_durations = {
        "Stuttgart": 2,
        "Bucharest": 2,
        "Geneva": 4,
        "Valencia": 6,
        "Munich": 7
    }
    
    # Define the allowed direct flight connections (undirected)
    allowed_flights = [
        frozenset(["Geneva", "Munich"]),
        frozenset(["Munich", "Valencia"]),
        frozenset(["Bucharest", "Valencia"]),
        frozenset(["Munich", "Bucharest"]),
        frozenset(["Valencia", "Stuttgart"]),
        frozenset(["Geneva", "Valencia"])
    ]
    
    # Time window constraints:
    # - Geneva: Must be visited such that at least one day of the Geneva stay falls between day 1 and day 4.
    # - Munich: Must be visited such that at least one day of the Munich stay falls between day 4 and day 10.
    
    def flight_connected(city1, city2):
        return frozenset([city1, city2]) in allowed_flights
    
    # Given an ordered route, assign day ranges.
    # Note: The first city uses its full duration; each subsequent city starts on the flight day
    # (which is the last day of the previous segment) and then adds (duration - 1) new days.
    def assign_itinerary(route):
        itinerary = []
        current_day = 1
        for idx, city in enumerate(route):
            duration = city_durations[city]
            if idx == 0:
                start_day = current_day
                end_day = start_day + duration - 1
            else:
                # The flight day is shared: current city starts on the previous segment's end day.
                start_day = current_day
                end_day = start_day + duration - 1
            itinerary.append({
                "city": city,
                "start_day": start_day,
                "end_day": end_day
            })
            current_day = end_day  # The end day becomes the shared flight day for next segment.
        return itinerary

    def satisfies_time_constraints(itinerary):
        # Overall itinerary must exactly cover 'total_days' unique days.
        if itinerary[-1]["end_day"] != total_days:
            return False
        for segment in itinerary:
            if segment["city"] == "Geneva":
                # To meet relatives, at least one day in Geneva must be between day 1 and day 4.
                if segment["start_day"] > 4:
                    return False
            if segment["city"] == "Munich":
                # Munich must have at least one day between day 4 and day 10.
                # This is true if the Munich segment [start, end] intersects [4, 10].
                if segment["start_day"] > 10 or segment["end_day"] < 4:
                    return False
        return True

    cities = list(city_durations.keys())
    valid_itinerary = None

    # Iterate over all permutations of cities.
    for route in itertools.permutations(cities):
        # Check if every consecutive pair in the route has a direct flight.
        valid_route = True
        for i in range(len(route) - 1):
            if not flight_connected(route[i], route[i+1]):
                valid_route = False
                break
        if not valid_route:
            continue
        
        # Assign day segments to the route.
        itinerary_assigned = assign_itinerary(route)
        # Verify that the total itinerary covers exactly 'total_days' unique days.
        if itinerary_assigned[-1]["end_day"] != total_days:
            continue
        
        # Check the time window constraints for Geneva and Munich.
        if not satisfies_time_constraints(itinerary_assigned):
            continue
        
        # Found a valid itinerary that meets all constraints.
        valid_itinerary = itinerary_assigned
        break

    # Build the output JSON structure.
    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        output_itinerary = []
        for segment in valid_itinerary:
            # Format the day range as "Day X-Y"
            day_range = f"Day {segment['start_day']}-{segment['end_day']}"
            output_itinerary.append({"day_range": day_range, "place": segment["city"]})
        result = {"itinerary": output_itinerary}
    
    print(json.dumps(result))

if __name__ == '__main__':
    main()