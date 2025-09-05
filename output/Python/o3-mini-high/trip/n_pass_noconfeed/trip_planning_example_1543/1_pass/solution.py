#!/usr/bin/env python3
import json
import sys

# Define the trip constraints as input variables

# Durations of stay in each city (number of days spent, counting the overlapping flight day)
durations = {
    "Prague": 3,
    "Warsaw": 4,
    "Dublin": 3,
    "Athens": 3,
    "Vilnius": 4,
    "Porto": 5,
    "London": 3,
    "Seville": 2,
    "Lisbon": 5,
    "Dubrovnik": 3
}

# Event constraints for some cities in the form (event_start, event_end)
# Meaning that at least one day of the city's visit (which spans from its start day to start+duration-1) 
# must fall within the event window.
event_constraints = {
    "Prague": (1, 3),      # Workshop in Prague must be between day 1 and 3.
    "London": (3, 5),      # Wedding in London between day 3 and 5.
    "Lisbon": (5, 9),      # Visit relatives in Lisbon between day 5 and 9.
    "Porto": (16, 20),     # Conference in Porto between day 16 and 20.
    "Warsaw": (20, 23)     # Meeting friends in Warsaw between day 20 and 23.
}
# For cities without an event constraint, we can consider that constraint as always satisfied.

# Total number of days in the overall itinerary.
total_days = 26

# Define the flight graph (bidirectional edges)
flight_graph = {
    "Warsaw": ["Vilnius", "London", "Athens", "Lisbon", "Porto", "Prague"],
    "Vilnius": ["Warsaw", "Athens"],
    "Prague": ["Athens", "Lisbon", "London", "Warsaw", "Dublin"],
    "Athens": ["Prague", "Vilnius", "Dublin", "Warsaw", "Dubrovnik", "Lisbon", "London"],
    "London": ["Lisbon", "Dublin", "Warsaw", "Prague", "Athens"],
    "Dublin": ["London", "Athens", "Seville", "Porto", "Prague", "Lisbon", "Dubrovnik"],
    "Seville": ["Dublin", "Porto", "Lisbon"],
    "Lisbon": ["London", "Porto", "Prague", "Athens", "Dublin", "Warsaw", "Seville"],
    "Porto": ["Lisbon", "Dublin", "Warsaw", "Seville"],
    "Dubrovnik": ["Athens", "Dublin"]
}

# List of all cities to be visited
all_cities = list(durations.keys())

# Global variable to hold a found valid itinerary order
solution_path = None

# Function to compute the day ranges (start_day, end_day) for a given itinerary order.
# By the rule: For the first city, start day = 1. For each subsequent city,
# the start day equals the previous city's end day (flight day overlap).
def compute_day_ranges(path):
    day_ranges = []
    current_day = 1
    for city in path:
        start = current_day
        end = start + durations[city] - 1
        day_ranges.append((start, end))
        # Next city starts on the same day as the current city's end (overlap flight day)
        current_day = end
    return day_ranges

# Check if the event constraint for a city is satisfied.
# The city's visit spans from start to end. For a constraint (e_start, e_end) to be met, there must be overlap.
def event_satisfied(city, start, end):
    if city not in event_constraints:
        return True
    e_start, e_end = event_constraints[city]
    # Check for any overlap between [start, end] and [e_start, e_end]
    if end < e_start or start > e_end:
        return False
    return True

# Backtracking search to find a valid itinerary order that satisfies flight connectivity and event constraints.
def backtrack(path, used):
    global solution_path
    if solution_path is not None:
        return  # Already found a solution

    # If the itinerary is complete, check the event constraints for all cities.
    if len(path) == len(all_cities):
        day_ranges = compute_day_ranges(path)
        # Check event constraints for each city in the itinerary
        all_ok = True
        for i, city in enumerate(path):
            start, end = day_ranges[i]
            if not event_satisfied(city, start, end):
                all_ok = False
                break
        # Also, check that the overall itinerary spans exactly total_days.
        if day_ranges[-1][1] != total_days:
            all_ok = False
        if all_ok:
            solution_path = path[:]
        return

    last_city = path[-1]
    # Try all cities not yet used that are directly reachable from last_city.
    for candidate in all_cities:
        if candidate in used:
            continue
        if candidate not in flight_graph.get(last_city, []):
            continue
        new_path = path + [candidate]
        # Compute day ranges for the new partial itinerary
        day_ranges = compute_day_ranges(new_path)
        # Check the event constraint for the candidate city (the last one added)
        cand_start, cand_end = day_ranges[-1]
        if not event_satisfied(candidate, cand_start, cand_end):
            continue
        # Also, for safety, check previous cities (they are fixed but we could re-check)
        valid_so_far = True
        for i, city in enumerate(new_path):
            s, e = day_ranges[i]
            if not event_satisfied(city, s, e):
                valid_so_far = False
                break
        if not valid_so_far:
            continue
        used.add(candidate)
        backtrack(new_path, used)
        if solution_path is not None:
            return
        used.remove(candidate)

# To reduce the search space and help satisfy early event constraints, we fix Prague as the first city.
initial_city = "Prague"
used = set([initial_city])
backtrack([initial_city], used)

# If a valid itinerary order was found, build the JSON-structured itinerary:
if solution_path is None:
    output = {"error": "No valid itinerary found with the given constraints."}
else:
    day_ranges = compute_day_ranges(solution_path)
    itinerary = []
    for city, (start, end) in zip(solution_path, day_ranges):
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    output = {"itinerary": itinerary}

# Output the result as JSON-formatted dictionary.
print(json.dumps(output))