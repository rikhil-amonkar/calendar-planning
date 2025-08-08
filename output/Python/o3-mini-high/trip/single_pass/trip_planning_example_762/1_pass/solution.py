#!/usr/bin/env python3
import itertools
import json

def main():
    # Input variables: city durations and special event constraints
    durations = {
        "Dublin": 3,   # days in Dublin
        "Madrid": 2,   # days in Madrid
        "Oslo": 3,     # days in Oslo
        "London": 2,   # days in London
        "Vilnius": 3,  # days in Vilnius
        "Berlin": 5    # days in Berlin
    }
    # Special event constraints: (min_day, max_day) they must occur during the city's interval.
    special_events = {
        "Madrid": (2, 3),  # Visit relatives in Madrid between day 2 and day 3.
        "Berlin": (3, 7),  # Attend wedding in Berlin between day 3 and day 7.
        "Dublin": (7, 9)   # Meet friends in Dublin between day 7 and day 9.
    }
    
    total_trip_days = 13  # total itinerary days

    # Direct flight connections (bidirectional)
    flight_graph = {
        "London": {"Madrid", "Oslo", "Dublin", "Berlin"},
        "Madrid": {"London", "Oslo", "Dublin", "Berlin"},
        "Oslo": {"Madrid", "London", "Berlin", "Dublin", "Vilnius"},
        "Dublin": {"Madrid", "Oslo", "London", "Berlin"},
        "Vilnius": {"Oslo", "Berlin"},
        "Berlin": {"Madrid", "Oslo", "Dublin", "London", "Vilnius"}
    }
    
    cities = list(durations.keys())
    valid_itinerary = None

    # Iterate over all possible orders of visiting the 6 cities.
    for order in itertools.permutations(cities):
        # Check if each adjacent pair has a direct flight connection.
        valid_route = True
        for i in range(len(order) - 1):
            if order[i+1] not in flight_graph[order[i]]:
                valid_route = False
                break
        if not valid_route:
            continue

        # Compute the schedule using overlapping flight days.
        # If you fly from city A to city B on day X, then day X counts for both A and B.
        schedule = []
        current_day = 1
        for idx, city in enumerate(order):
            start_day = current_day
            end_day = start_day + durations[city] - 1
            schedule.append((city, start_day, end_day))
            # For next city, the flight happens on the last day of current city's interval.
            if idx < len(order) - 1:
                current_day = end_day

        # Check that the overall itinerary spans the required total trip days.
        # Total days = sum(durations) - (number_of_flights), here number_of_flights = 5.
        # For sanity check, the last city's end_day must equal total_trip_days.
        if schedule[-1][2] != total_trip_days:
            continue

        # Validate special event time constraints:
        meets_events = True
        # Create a mapping from city to its scheduled interval.
        schedule_dict = {city: (start, end) for city, start, end in schedule}
        for event_city, (event_min, event_max) in special_events.items():
            # The itinerary must include the city; it always will since we permute over all cities.
            # Check if the city's scheduled interval intersects with the event window.
            if event_city in schedule_dict:
                city_start, city_end = schedule_dict[event_city]
                # Intersection condition: city_start <= event_max and city_end >= event_min
                if not (city_start <= event_max and city_end >= event_min):
                    meets_events = False
                    break
        if not meets_events:
            continue

        # Found a valid itinerary meeting all constraints.
        valid_itinerary = schedule
        break

    # If a valid itinerary is found, format it into the required JSON format.
    if valid_itinerary:
        output_itinerary = []
        for city, start, end in valid_itinerary:
            day_range = f"Day {start}-{end}"
            output_itinerary.append({"day_range": day_range, "place": city})
        result = {"itinerary": output_itinerary}
    else:
        result = {"itinerary": []}

    print(json.dumps(result))

if __name__ == '__main__':
    main()