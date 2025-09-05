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
# For example, "Riga" to "Munich" is treated as a bidirectional connection.
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

# Check direct flight connectivity (undirected)
def is_connected(city_a, city_b):
    return frozenset((city_a, city_b)) in flights

# Time constraints:
# Each city’s stay starts on a given day and lasts for its duration;
# certain cities have requirements on when their stay must occur.
def time_constraint(city, start_day):
    # For a city with duration d, the stay is from start_day to start_day + d - 1.
    if city == "Vienna":
        # Must meet friend between day 1 and 5; at least one day of the stay must fall in [1,5].
        return start_day <= 5
    elif city == "Prague":
        # Must attend a show from day 5 to 9; with duration 5 the only possibility is start_day == 5.
        return start_day == 5
    elif city == "Stockholm":
        # Conference on days 16 and 17; with duration 2 we require start_day == 16.
        return start_day == 16
    elif city == "Split":
        # Must visit relatives between day 11 and 13.
        # Stay covers [start_day, start_day+2]; require this interval intersects [11, 13].
        return (start_day <= 13) and ((start_day + 2) >= 11)
    elif city == "Riga":
        # Meet friends between day 15 and 16.
        # Stay covers [start_day, start_day+1]; require intersection with [15, 16].
        return (start_day <= 16) and ((start_day + 1) >= 15)
    else:
        return True

# Compute the start day for the next city given the current order.
# By definition: start for the first city is 1, and for each city we add (duration - 1)
# because the flight day overlaps with the previous city’s last day.
def next_start_day(order):
    effective = sum(durations[city] - 1 for city in order)
    return 1 + effective

# Backtracking search for a valid itinerary order.
def backtrack(order, available, solution_found):
    # Stop early if a solution is already found.
    if solution_found[0] is not None:
        return

    # Base case: when all cities are scheduled, check if the itinerary finishes on Day 20.
    if len(order) == len(durations):
        total_days = next_start_day(order)  # The final itinerary day.
        if total_days == 20:
            solution_found[0] = order[:]
        return

    current_start = next_start_day(order)
    last_city = order[-1]
    for city in sorted(available):
        # Only add candidate if there is a direct flight from the last city.
        if not is_connected(last_city, city):
            continue

        # Check if adding this city starting on current_start satisfies its time constraint.
        if not time_constraint(city, current_start):
            continue

        order.append(city)
        next_available = available - {city}
        backtrack(order, next_available, solution_found)
        if solution_found[0] is not None:
            return
        order.pop()

def main():
    # To reduce the search space, force Vienna as the first city and Prague as the second.
    # (Vienna must start on day 1; Prague’s constraint forces it to start on day 5.)
    initial_order = ["Vienna", "Prague"]
    remaining = set(durations.keys()) - set(initial_order)
    
    if not time_constraint("Vienna", 1):
        sys.exit("Vienna does not meet time constraints when placed first.")
    if not time_constraint("Prague", next_start_day(["Vienna"])):
        sys.exit("Prague does not meet time constraints when placed second.")
    
    solution_found = [None]
    backtrack(initial_order, remaining, solution_found)
    
    if solution_found[0] is None:
        sys.exit("No valid itinerary found.")
    
    # Build the itinerary showing for each city its day range.
    itinerary = []
    cumulative = 0
    for city in solution_found[0]:
        start = 1 + cumulative
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        cumulative += durations[city] - 1

    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()

--------------------------------------------------

Key fix:
• In the backtracking base case, we now compute:
  total_days = next_start_day(order)
  if total_days == 20: solution_found[0] = order[:]

This ensures that when all cities are scheduled the itinerary runs exactly from Day 1 through Day 20.

With this correction the code no longer exits with “No valid itinerary found.” Enjoy!