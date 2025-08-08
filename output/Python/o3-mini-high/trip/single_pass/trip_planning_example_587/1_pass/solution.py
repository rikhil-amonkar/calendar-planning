#!/usr/bin/env python3
import json
import itertools

def main():
    # Input variables: total days, durations, event constraints, and flight graph.
    total_days = 21

    # Required days in each city (the “city‐days” if counted with overlaps)
    durations = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2
    }

    # Event constraints: tuple values indicate the required day window (inclusive)
    # Wedding in Manchester between day 1 and day 3; Workshop in Venice between day 3 and day 9.
    events = {
        "Manchester": (1, 3),
        "Venice": (3, 9)
    }

    # Define the direct flight connections (bidirectional edges)
    flight_graph = {
        "Manchester": ["Venice", "Istanbul", "Krakow"],
        "Venice": ["Manchester", "Istanbul", "Lyon"],
        "Istanbul": ["Manchester", "Venice", "Krakow", "Lyon"],
        "Krakow": ["Manchester", "Istanbul"],
        "Lyon": ["Venice", "Istanbul"]
    }

    # We have five cities. The itinerary must start with Manchester because of the wedding.
    all_cities = list(durations.keys())
    start_city = "Manchester"
    remaining_cities = [city for city in all_cities if city != start_city]
    
    valid_itinerary = None
    valid_schedule = None

    # Try all permutations of the remaining cities.
    for perm in itertools.permutations(remaining_cities):
        route = [start_city] + list(perm)
        
        # Check if every consecutive flight is available.
        valid_route = True
        for i in range(len(route) - 1):
            if route[i+1] not in flight_graph[route[i]]:
                valid_route = False
                break
        if not valid_route:
            continue
        
        # Compute the itinerary schedule using overlapping flight days.
        # Rule: For the first city, the start day is 1. For every flight from city A to B on day X,
        # day X is counted for both A and B.
        schedule = []  # Each element is a tuple (city, start_day, end_day)
        current_day = 1
        route_valid = True

        for city in route:
            start_day = current_day
            # The city is visited for a fixed duration.
            end_day = start_day + durations[city] - 1
            # If there's an event constraint for the city, check that the event window is met.
            if city in events:
                event_start, event_end = events[city]
                # There must be at least one day in common between [start_day, end_day] and [event_start, event_end]
                if end_day < event_start or start_day > event_end:
                    route_valid = False
                    break
            schedule.append((city, start_day, end_day))
            # Update the current day. The flight day is the end_day, which counts for both cities.
            current_day = end_day

        if not route_valid:
            continue

        # Check the total distinct days matches the planned total.
        if schedule[-1][2] != total_days:
            continue

        # Found a valid itinerary schedule.
        valid_itinerary = route
        valid_schedule = schedule
        break

    # If no valid itinerary is found, output an empty itinerary.
    if valid_schedule is None:
        output = {"itinerary": []}
    else:
        # Format the schedule into day_range and place mappings.
        itinerary_list = []
        for city, start_day, end_day in valid_schedule:
            itinerary_list.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
        output = {"itinerary": itinerary_list}
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()