#!/usr/bin/env python3
import json
import itertools

def main():
    total_days = 12

    # Required durations (city: number of days)
    durations = {
        "Frankfurt": 3,
        "Naples": 4,
        "Helsinki": 4,
        "Lyon": 3,
        "Prague": 2
    }

    # Define direct flight connections as undirected pairs
    flights = [
        ("Prague", "Lyon"),
        ("Prague", "Frankfurt"),
        ("Frankfurt", "Lyon"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Prague", "Helsinki")
    ]
    flight_set = set(frozenset(pair) for pair in flights)

    # Event constraints:
    # Workshop in Prague must be attended between day 1 and day 2.
    # Annual show in Helsinki is from day 2 to day 5.
    # To satisfy these, we require that Prague is visited first (so day 1 is in Prague)
    # and Helsinki is visited second (so its 4-day window is Day 2-5).
    fixed_order = ["Prague", "Helsinki"]

    # The remaining cities to schedule are Frankfurt, Naples, and Lyon.
    remaining_cities = [city for city in durations if city not in fixed_order]

    possible_orders = []
    for perm in itertools.permutations(remaining_cities):
        order = fixed_order + list(perm)
        valid = True
        # Check direct flight connectivity for each consecutive pair.
        for i in range(len(order) - 1):
            if frozenset({order[i], order[i+1]}) not in flight_set:
                valid = False
                break
        if valid:
            possible_orders.append(order)

    # If no valid itinerary is found, output an empty itinerary.
    if not possible_orders:
        print(json.dumps({"itinerary": []}))
        return

    # Choose the first valid itinerary (this can be extended with additional optimality criteria if needed)
    optimal_order = possible_orders[0]

    # Compute itinerary day ranges.
    # Rule: The first city's start day is 1. If one flies from city A to B on day X,
    # then day X is counted for both A and B. So, next city's start day equals previous city's end day.
    itinerary = []
    current_day = 1
    for city in optimal_order:
        d = durations[city]
        end_day = current_day + d - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
        current_day = end_day  # Overlap on the flight day

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()