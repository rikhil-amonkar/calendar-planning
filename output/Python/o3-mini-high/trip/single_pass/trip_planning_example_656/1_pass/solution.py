#!/usr/bin/env python3
import itertools
import json

def main():
    # Trip parameters
    total_trip_days = 19
    durations = {
        "Reykjavik": 5,
        "Istanbul": 4,
        "Edinburgh": 5,
        "Oslo": 2,
        "Stuttgart": 3,
        "Bucharest": 5
    }
    cities = list(durations.keys())

    # Define direct flight connections (assumed bidirectional)
    flight_graph = {
        "Bucharest": {"Oslo", "Istanbul"},
        "Oslo": {"Bucharest", "Istanbul", "Reykjavik", "Edinburgh"},
        "Istanbul": {"Bucharest", "Oslo", "Edinburgh", "Stuttgart"},
        "Reykjavik": {"Oslo", "Stuttgart"},  # "from Reykjavik to Stuttgart" assumed bidirectional
        "Stuttgart": {"Reykjavik", "Istanbul", "Edinburgh"},
        "Edinburgh": {"Oslo", "Stuttgart", "Istanbul"}
    }

    # Constraint: Meet friends in Istanbul between Day 5 and Day 8
    # Istanbul's visit (computed as start_day to end_day) must overlap with days 5-8.
    # Constraint: Visit relatives in Oslo between Day 8 and Day 9.
    # Oslo's visit must overlap with days 8-9.

    # Compute the schedule for a given order.
    # If a flight occurs on day X, then X counts for both cities.
    # For the first city, days = 1 to duration.
    # For each subsequent city, the start day equals the previous city's end day.
    def compute_schedule(order):
        schedule = []
        current_day = 1
        for city in order:
            start_day = current_day
            end_day = start_day + durations[city] - 1
            schedule.append((city, start_day, end_day))
            # The flight day is overlapping; update current_day to end_day.
            current_day = end_day
        return schedule

    # Check direct flight transitions in the order
    def valid_transitions(order):
        for i in range(1, len(order)):
            if order[i] not in flight_graph.get(order[i-1], set()):
                return False
        return True

    # Check if the schedule meets the Istanbul and Oslo constraints.
    def meets_constraints(schedule):
        for city, start, end in schedule:
            if city == "Istanbul":
                # Must be in Istanbul on a day between day 5 and 8 
                # i.e., the visit must cover at least one day d with 5 <= d <= 8.
                if not (start <= 8 and end >= 5):
                    return False
            if city == "Oslo":
                # Must be in Oslo on a day between day 8 and 9.
                if not (start <= 9 and end >= 8):
                    return False
        return True

    valid_itinerary = None
    # Iterate over all permutations of cities
    for order in itertools.permutations(cities):
        if valid_transitions(order):
            sched = compute_schedule(order)
            if meets_constraints(sched):
                valid_itinerary = sched
                break

    # Build output itinerary in the required JSON format.
    itinerary_list = []
    if valid_itinerary:
        for city, start, end in valid_itinerary:
            itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()