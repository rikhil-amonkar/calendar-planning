#!/usr/bin/env python3
import json
import sys

# Define the cities with their required durations and (if applicable) fixed start days.
# The fixed_start value indicates the required start day for that city's visit, if needed.
cities = {
    "Edinburgh": {"duration": 5, "fixed_start": 1},     # Must meet friend between Day 1-5, so start at 1.
    "Budapest": {"duration": 5, "fixed_start": 9},       # Annual show from Day 9-13; only 5-day window that covers it is 9-13.
    "Munich": {"duration": 3, "fixed_start": 18},        # Workshop between Day 18-20; forces visit on 18-20.
    "Stockholm": {"duration": 2, "fixed_start": 17},     # Meeting with friends between Day 17-18 (choose window 17-18).
    "Warsaw": {"duration": 5, "fixed_start": 25},        # Conference from Day 25-29.
    "Barcelona": {"duration": 5, "fixed_start": None},
    "Krakow": {"duration": 4, "fixed_start": None},
    "Bucharest": {"duration": 2, "fixed_start": None},
    "Riga": {"duration": 5, "fixed_start": None},
    "Vienna": {"duration": 5, "fixed_start": None},
}

# Total trip days required (using the rule: total city-days - (# of flights) = total days).
TOTAL_TRIP_DAY = 32

# List of direct flight edges between cities (treating flights as bidirectional).
edges = [
    ("Budapest", "Munich"),
    ("Bucharest", "Riga"),
    ("Munich", "Krakow"),
    ("Munich", "Warsaw"),
    ("Munich", "Bucharest"),
    ("Edinburgh", "Stockholm"),
    ("Barcelona", "Warsaw"),
    ("Edinburgh", "Krakow"),
    ("Barcelona", "Munich"),
    ("Stockholm", "Krakow"),
    ("Budapest", "Vienna"),
    ("Barcelona", "Stockholm"),
    ("Stockholm", "Munich"),
    ("Edinburgh", "Budapest"),
    ("Barcelona", "Riga"),
    ("Edinburgh", "Barcelona"),
    ("Vienna", "Riga"),
    ("Barcelona", "Budapest"),
    ("Bucharest", "Warsaw"),
    ("Vienna", "Krakow"),
    ("Edinburgh", "Riga"),
    ("Vienna", "Stockholm"),
    ("Warsaw", "Krakow"),
    ("Barcelona", "Krakow"),
    ("Riga", "Munich"),
    ("Riga", "Vienna"),
    ("Riga", "Bucharest"),
    ("Budapest", "Warsaw"),
    ("Vienna", "Warsaw"),
    ("Barcelona", "Vienna"),
    ("Budapest", "Bucharest"),
    ("Vienna", "Munich"),
    ("Riga", "Warsaw"),
    ("Stockholm", "Riga"),
    ("Stockholm", "Warsaw")
]

# Build the flight connectivity graph (bidirectional)
graph = {}
for city in cities:
    graph[city] = set()

for a, b in edges:
    graph[a].add(b)
    graph[b].add(a)

# Backtracking search variables
solution_plan = None  # Will hold the first valid itinerary found

# Recursive backtracking search.
# 'index' is the position in the itinerary (0-based).
# 'current_start' is the start day for the next segment.
# 'current_plan' is a list of tuples: (city, start_day, end_day).
# 'used' is the set of cities already placed.
def search(index, current_start, current_plan, used):
    global solution_plan
    # If we have assigned all 10 cities, check if the last segment ends exactly on TOTAL_TRIP_DAY.
    if index == len(cities):
        if current_start == TOTAL_TRIP_DAY:
            solution_plan = current_plan.copy()
        return

    for city in cities:
        if city in used:
            continue
        # Force Edinburgh to be the first city (to satisfy meeting friend in Edinburgh early).
        if index == 0 and city != "Edinburgh":
            continue

        # If not the first segment, check flight connectivity from the previous city.
        if index > 0:
            prev_city = current_plan[-1][0]
            if city not in graph[prev_city]:
                continue

        # Determine the start day for this city's segment (by rule, it is the current_start).
        candidate_start = current_start

        # If the city has a fixed required start day, enforce that.
        fixed = cities[city]["fixed_start"]
        if fixed is not None and fixed != candidate_start:
            continue

        # Compute the end day for this city.
        duration = cities[city]["duration"]
        candidate_end = candidate_start + duration - 1

        # Prepare new plan data.
        current_plan.append((city, candidate_start, candidate_end))
        used.add(city)

        # Next segment's start day is the candidate_end (flight day counts for both cities).
        search(index + 1, candidate_end, current_plan, used)
        if solution_plan is not None:
            return  # Stop if a solution is found.

        current_plan.pop()
        used.remove(city)

# Start the search
search(0, 1, [], set())

# Prepare the itinerary in the JSON output format.
# Each segment is represented with a day range (e.g., "Day 1-5") and the city name.
itinerary = []
if solution_plan is not None:
    for (city, start_day, end_day) in solution_plan:
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })

output = {"itinerary": itinerary}

# Output as JSON.
print(json.dumps(output, indent=2))