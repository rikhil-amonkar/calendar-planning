#!/usr/bin/env python3
import itertools
import json

def compute_schedule(itinerary, durations):
    # Compute the day ranges for each city in the itinerary.
    # The trip starts on day 1. For the first city, days = [1, d].
    # For each subsequent city, the start day equals the previous city's end day (flight day overlap).
    schedule = []
    current_day = 1
    for city in itinerary:
        start_day = current_day
        end_day = start_day + durations[city] - 1
        schedule.append((city, start_day, end_day))
        # Flight from current city to next city happens on the end_day.
        current_day = end_day
    return schedule

def check_events(schedule):
    # Check event constraints on the computed schedule.
    # Constraint for Bucharest (4-day stay): Visit relatives between day 1 and day 4.
    #   Thus at least one day of Bucharest must fall in the interval [1, 4].
    # Constraint for Munich (5-day stay): Attend the wedding between day 4 and day 8.
    #   So Munich's span must intersect with [4, 8].
    # Constraint for Seville (5-day stay): Meet friends between day 8 and day 12.
    #   So Seville's span must intersect with [8, 12].
    for city, start, end in schedule:
        if city == "Bucharest":
            # Intersection of Bucharest's days [start, end] with [1,4] must be non-empty.
            if max(start, 1) > min(end, 4):
                return False
        elif city == "Munich":
            if max(start, 4) > min(end, 8):
                return False
        elif city == "Seville":
            if max(start, 8) > min(end, 12):
                return False
    return True

def check_connectivity(itinerary, flight_graph):
    # Check that each consecutive pair of cities has a direct flight.
    for i in range(len(itinerary) - 1):
        current_city = itinerary[i]
        next_city = itinerary[i + 1]
        if next_city not in flight_graph[current_city]:
            return False
    return True

def main():
    # Input parameters.
    total_days = 18
    durations = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2
    }
    # List of cities.
    cities = list(durations.keys())
    # Direct flight connections between cities (bidirectional).
    flight_graph = {
        "Milan": ["Stockholm", "Munich", "Seville"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Munich": ["Bucharest", "Stockholm", "Seville", "Milan", "Tallinn"],
        "Bucharest": ["Munich"],
        "Seville": ["Munich", "Milan"],
        "Tallinn": ["Stockholm", "Munich"]
    }
    # Event constraints:
    # - Bucharest: relatives between day 1 and day 4.
    # - Munich: wedding between day 4 and day 8.
    # - Seville: meet friends between day 8 and day 12.
    valid_itinerary = None
    valid_schedule = None

    # Iterate over all permutations of the cities.
    for perm in itertools.permutations(cities):
        # Check connectivity using direct flights.
        if not check_connectivity(perm, flight_graph):
            continue

        # Compute schedule based on durations and flight overlap.
        schedule = compute_schedule(perm, durations)
        # The final end day must equal total_days (it will because total_days = sum(durations) - (n - 1)).
        if schedule[-1][2] != total_days:
            continue

        # Check if the schedule meets the event constraints.
        if not check_events(schedule):
            continue

        valid_itinerary = perm
        valid_schedule = schedule
        break

    if valid_schedule is None:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        for city, start, end in valid_schedule:
            day_range = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_list}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()