#!/usr/bin/env python3
import json
import sys

# Define the cities and their required durations.
durations = {
    "Prague": 3,
    "London": 3,
    "Lisbon": 5,
    "Porto": 5,
    "Warsaw": 4,
    "Dublin": 3,
    "Athens": 3,
    "Vilnius": 4,
    "Seville": 2,
    "Dubrovnik": 3
}

# Event constraints: each event is specified as (earliest_day, latest_day)
# The city’s visit (its interval) must intersect the time window.
event_constraints = {
    "Prague": (1, 3),      # workshop between day 1 and 3
    "London": (3, 5),      # wedding between day 3 and 5
    "Lisbon": (5, 9),      # visit relatives between day 5 and 9
    "Porto": (16, 20),     # conference between day 16 and 20
    "Warsaw": (20, 23)     # meet friends between day 20 and 23
}

# List of all cities.
cities = list(durations.keys())

# Build the flight graph (bidirectional) based on the provided direct flights.
# Flight pairs are given as strings "CityA and CityB"
flights_list = [
    ("Warsaw", "Vilnius"),
    ("Prague", "Athens"),
    ("London", "Lisbon"),
    ("Lisbon", "Porto"),
    ("Prague", "Lisbon"),
    ("London", "Dublin"),
    ("Athens", "Vilnius"),
    ("Athens", "Dublin"),
    ("Prague", "London"),
    ("London", "Warsaw"),
    ("Dublin", "Seville"),
    ("Seville", "Porto"),
    ("Lisbon", "Athens"),
    ("Dublin", "Porto"),
    ("Athens", "Warsaw"),
    ("Lisbon", "Warsaw"),
    ("Porto", "Warsaw"),
    ("Prague", "Warsaw"),
    ("Prague", "Dublin"),
    ("Athens", "Dubrovnik"),
    ("Lisbon", "Dublin"),
    ("Dubrovnik", "Dublin"),
    ("Lisbon", "Seville"),
    ("London", "Athens")
]

# Initialize flight graph: each city maps to a set of directly connected cities.
flight_graph = { city: set() for city in cities }
for (a, b) in flights_list:
    flight_graph[a].add(b)
    flight_graph[b].add(a)

# Function to compute the start and end days for each city in an itinerary.
# Using the rule: start_day[0] = 1, and for i>=1,
#  start_day[i] = 1 + (sum_{j=0}^{i-1} durations[order[j]]) - i
def compute_intervals(order):
    intervals = []
    current_day = 1
    for i, city in enumerate(order):
        # For the first city, start is day 1.
        # For subsequently, because flying on the departure day counts in both cities,
        # we subtract 1 for each transition.
        if i == 0:
            start_day = 1
        else:
            # start_day = previous end_day + 1, but since flight day is counted twice,
            # we have: start_day = (prev_start + duration(prev) - 1) + 1 = prev_start + duration(prev)
            # Alternatively, using the formula:
            start_day = 1 + sum(durations[c] for c in order[:i]) - i
        end_day = start_day + durations[city] - 1
        intervals.append((start_day, end_day))
    return intervals

# Check whether an interval [start, end] intersects a given event window [win_start, win_end].
def interval_satisfies(start, end, win_start, win_end):
    return start <= win_end and end >= win_start

# Backtracking search for a valid ordering.
# We fix the first three cities to satisfy early events: Prague, London and Lisbon.
fixed_prefix = ["Prague", "London", "Lisbon"]

# The remaining cities are those not in the fixed prefix.
remaining_cities = [city for city in cities if city not in fixed_prefix]

# We want a total itinerary that uses all 10 cities.
num_cities = len(cities)

# Global variable to store a solution itinerary when found.
solution_order = None

def backtrack(order, remaining):
    global solution_order
    if solution_order is not None:
        return  # already found a solution
    # If the order is complete, check event constraints and overall days.
    if not remaining:
        intervals = compute_intervals(order)
        # Check event constraints for cities that have events.
        for idx, city in enumerate(order):
            if city in event_constraints:
                win_start, win_end = event_constraints[city]
                start_day, end_day = intervals[idx]
                if not interval_satisfies(start_day, end_day, win_start, win_end):
                    return
        # Also, the overall itinerary end day should be 26.
        if intervals[-1][1] != 26:
            return
        # Found a valid solution.
        solution_order = order.copy()
        return

    # For the next city, enforce flight connectivity.
    last_city = order[-1]
    # Order remaining cities in a stable order for consistency.
    for candidate in remaining:
        if candidate not in flight_graph[last_city]:
            continue  # cannot fly directly from last_city to candidate
        # Tentatively add the candidate.
        new_order = order + [candidate]
        # Compute the current interval for the newly added candidate.
        current_intervals = compute_intervals(new_order)
        idx = len(new_order) - 1
        city = new_order[idx]
        # If this city has an event constraint, check if its interval (so far) can satisfy it.
        if city in event_constraints:
            win_start, win_end = event_constraints[city]
            start_day, end_day = current_intervals[idx]
            # If the city’s scheduled interval does not intersect the event window, prune.
            if not interval_satisfies(start_day, end_day, win_start, win_end):
                continue
        # Prune if the itinerary is already too long.
        # The minimal total days if we add the remaining cities (optimistically, maximum overlap)
        current_total = current_intervals[-1][1]
        # Remaining extra days if all remaining cities were added fully
        extra = sum(durations[r] for r in remaining if r != candidate) - (len(remaining) - 1)
        if current_total + extra > 26:
            # It might overshoot 26; however, since total days is fixed (35 - 9 = 26) for any full itinerary,
            # we can use the fact that the sum of durations is fixed.
            pass

        new_remaining = remaining.copy()
        new_remaining.remove(candidate)
        backtrack(new_order, new_remaining)
        if solution_order is not None:
            return

# Start backtracking with the fixed prefix.
backtrack(fixed_prefix, remaining_cities)

if solution_order is None:
    # No valid itinerary found.
    result = {"itinerary": []}
else:
    # Compute intervals for the found ordering.
    intervals = compute_intervals(solution_order)
    itinerary = []
    for city, (start, end) in zip(solution_order, intervals):
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
    result = {"itinerary": itinerary}

# Output the result as JSON.
print(json.dumps(result))
sys.exit(0)