#!/usr/bin/env python3
import itertools
import json

def compute_intervals(order, durations):
    # Compute effective day intervals given the ordering and city durations.
    # If a flight happens on a day X, that day counts for both cities.
    intervals = []
    current_start = 1
    for city in order:
        duration = durations[city]
        end_day = current_start + duration - 1
        intervals.append((current_start, end_day))
        # Next city starts on the same day as the flight day (end_day)
        current_start = end_day
    return intervals

def valid_flight_connections(order, flight_connections):
    # Check that each adjacent pair in the itinerary has a direct flight.
    for i in range(len(order) - 1):
        if frozenset([order[i], order[i+1]]) not in flight_connections:
            return False
    return True

def valid_event_constraints(order, intervals):
    # Wedding in Zurich must be attended between day 1 and day 3.
    if "Zurich" in order:
        idx = order.index("Zurich")
        start, end = intervals[idx]
        # We require that some day in Zurich falls in the window [1, 3]
        if start > 3:
            return False
    else:
        return False

    # Conference in Split must be attended on day 4 and day 10.
    # Thus the effective interval in Split must include both day 4 and day 10.
    if "Split" in order:
        idx = order.index("Split")
        start, end = intervals[idx]
        if start > 4 or end < 10:
            return False
    else:
        return False

    return True

def main():
    total_days = 12
    # Define the cities and their required effective durations.
    cities = ["Hamburg", "Zurich", "Helsinki", "Bucharest", "Split"]
    durations = {
        "Hamburg": 2,
        "Zurich": 3,
        "Helsinki": 2,
        "Bucharest": 2,
        "Split": 7
    }
    # Define available direct flight connections (treated as undirected edges).
    flight_connections = set([
        frozenset(["Zurich", "Helsinki"]),
        frozenset(["Hamburg", "Bucharest"]),
        frozenset(["Helsinki", "Hamburg"]),
        frozenset(["Zurich", "Hamburg"]),
        frozenset(["Zurich", "Bucharest"]),
        frozenset(["Zurich", "Split"]),
        frozenset(["Helsinki", "Split"]),
        frozenset(["Split", "Hamburg"]),
    ])

    best_itinerary = None
    # Iterate over all possible orders (permutations) of the cities.
    for order in itertools.permutations(cities):
        intervals = compute_intervals(order, durations)
        # The final end day should equal total_days.
        if intervals[-1][1] != total_days:
            continue
        if not valid_flight_connections(order, flight_connections):
            continue
        if not valid_event_constraints(order, intervals):
            continue
        # Found a valid itinerary order.
        itinerary = []
        for city, (start, end) in zip(order, intervals):
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
        best_itinerary = itinerary
        break

    if best_itinerary is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": best_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()