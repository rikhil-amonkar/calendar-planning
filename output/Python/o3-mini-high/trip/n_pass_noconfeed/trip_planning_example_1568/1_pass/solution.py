#!/usr/bin/env python3
import json
import sys

# Define the cities with their required durations (in days)
durations = {
    "Vienna": 5,
    "Prague": 5,
    "Munich": 2,
    "Split": 3,
    "Amsterdam": 3,
    "Istanbul": 2,
    "Riga": 2,
    "Stockholm": 2,
    "Brussels": 2,
    "Seville": 3
}

# Flight network as a set of undirected connections using frozensets.
# Note: "from Riga to Munich" is treated as a bidirectional connection.
flights = {
    frozenset(("Riga", "Stockholm")),
    frozenset(("Stockholm", "Brussels")),
    frozenset(("Istanbul", "Munich")),
    frozenset(("Istanbul", "Riga")),
    frozenset(("Prague", "Split")),
    frozenset(("Vienna", "Brussels")),
    frozenset(("Vienna", "Riga")),
    frozenset(("Split", "Stockholm")),
    frozenset(("Munich", "Amsterdam")),
    frozenset(("Split", "Amsterdam")),
    frozenset(("Amsterdam", "Stockholm")),
    frozenset(("Amsterdam", "Riga")),
    frozenset(("Vienna", "Stockholm")),
    frozenset(("Vienna", "Istanbul")),
    frozenset(("Vienna", "Seville")),
    frozenset(("Istanbul", "Amsterdam")),
    frozenset(("Munich", "Brussels")),
    frozenset(("Prague", "Munich")),
    frozenset(("Riga", "Munich")),
    frozenset(("Prague", "Amsterdam")),
    frozenset(("Prague", "Brussels")),
    frozenset(("Prague", "Istanbul")),
    frozenset(("Istanbul", "Stockholm")),
    frozenset(("Vienna", "Prague")),
    frozenset(("Munich", "Split")),
    frozenset(("Vienna", "Amsterdam")),
    frozenset(("Prague", "Stockholm")),
    frozenset(("Brussels", "Seville")),
    frozenset(("Munich", "Stockholm")),
    frozenset(("Istanbul", "Brussels")),
    frozenset(("Amsterdam", "Seville")),
    frozenset(("Vienna", "Split")),
    frozenset(("Munich", "Seville")),
    frozenset(("Riga", "Brussels")),
    frozenset(("Prague", "Riga")),
    frozenset(("Vienna", "Munich"))
}

# Function to check direct flight connectivity (undirected)
def is_connected(city_a, city_b):
    return frozenset((city_a, city_b)) in flights

# Time constraint function for each city.
# Given a candidate city and the start day (of its segment), returns True if the city's time constraints are met.
def time_constraint(city, start_day):
    # For a city with duration d, the stay is from start_day to (start_day + d - 1)
    if city == "Vienna":
        # Must meet friend between day 1 and 5; require that at least one day of the interval [start, start+4] is in [1,5].
        # We'll require start_day <= 5.
        return start_day <= 5
    elif city == "Prague":
        # Must attend a show from day 5 to 9; with duration 5 the only possibility is that start_day == 5.
        return start_day == 5
    elif city == "Stockholm":
        # Conference on days 16 and 17; with duration 2 we require start_day == 16.
        return start_day == 16
    elif city == "Split":
        # Must visit relatives between day 11 and 13.
        # Stay covers [start_day, start_day + 2]. We require that this interval intersects [11, 13].
        return (start_day <= 13) and ((start_day + 2) >= 11)
    elif city == "Riga":
        # Meet friends between day 15 and 16.
        # Stay covers [start_day, start_day + 1]. Require intersection with [15, 16].
        return (start_day <= 16) and ((start_day + 1) >= 15)
    else:
        return True

# Given the current order, compute the start day for the next city.
# The start day for the first city is 1.
def next_start_day(order):
    # current_effective = sum(durations[city] - 1 for city in order)
    effective = 0
    for city in order:
        effective += durations[city] - 1
    return 1 + effective

# Backtracking search for a valid itinerary order.
def backtrack(order, available, solution_found):
    # If a valid itinerary has been found, propagate it.
    if solution_found[0] is not None:
        return

    if len(order) == len(durations):
        # Complete ordering, check final itinerary day is 20.
        total_days = next_start_day(order) - 1  # last city ends at start + duration - 1 = next_start - 1
        if total_days == 20:
            solution_found[0] = order[:]
        return

    current_start = next_start_day(order)
    last_city = order[-1]
    for city in sorted(available):
        # Check flight connectivity from the last city to candidate city.
        if not is_connected(last_city, city):
            continue

        # The candidate city's segment will start at current_start.
        if not time_constraint(city, current_start):
            continue

        # Choose city and proceed.
        order.append(city)
        next_available = available - {city}
        backtrack(order, next_available, solution_found)
        if solution_found[0] is not None:
            return
        order.pop()

def main():
    # To reduce the search space, force Vienna as the first city and Prague as the second.
    # Because Prague's time constraint forces its start day to be 5 and a 5-day Vienna starting on day 1 gives that.
    initial_order = ["Vienna", "Prague"]
    remaining = set(durations.keys()) - set(initial_order)
    # Check that Vienna and Prague satisfy their constraints in the fixed positions.
    if not time_constraint("Vienna", 1):
        sys.exit("Vienna does not meet time constraints when placed first.")
    if not time_constraint("Prague", next_start_day(["Vienna"])):
        sys.exit("Prague does not meet time constraints when placed second.")
    
    solution_found = [None]
    backtrack(initial_order, remaining, solution_found)
    
    if solution_found[0] is None:
        sys.exit("No valid itinerary found.")
    
    # Build the itinerary with day ranges.
    itinerary = []
    current_day = 1
    for city in solution_found[0]:
        d = durations[city]
        start = current_day
        end = start + d - 1
        # Append the mapping with day range and place.
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        # Next city's start day is the same as the current city's end day (flight day overlap)
        current_day = end
    # Adjust the itinerary's day ranges based on the rule:
    # Actually, the calculation above already uses: next start = previous start + (duration - 1).
    # Let's recompute properly:
    itinerary = []
    cumulative = 0
    for city in solution_found[0]:
        start = 1 + cumulative
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        cumulative += (durations[city] - 1)
    
    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()