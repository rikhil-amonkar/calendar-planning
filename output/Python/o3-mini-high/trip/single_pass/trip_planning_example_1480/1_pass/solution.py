#!/usr/bin/env python3
import json
import itertools

# Define the cities and their required durations (in days)
# The sum of required durations is 36 days.
durations = {
    "Istanbul": 4,
    "Vienna": 4,
    "Riga": 2,
    "Brussels": 2,
    "Madrid": 4,
    "Vilnius": 4,
    "Venice": 5,
    "Geneva": 4,
    "Munich": 5,
    "Reykjavik": 2
}

# Define the special time-window constraints.
# Each constraint is expressed as a tuple (min_day, max_day)
time_windows = {
    "Geneva": (1, 4),    # visit relatives in Geneva between day 1 and day 4
    "Venice": (7, 11),   # attend workshop in Venice between day 7 and day 11
    "Vilnius": (20, 23), # meet friends in Vilnius between day 20 and day 23
    "Brussels": (26, 27) # attend wedding in Brussels between day 26 and day 27
}

# Define the direct flights as edges.
# We assume that "and" or "from" means a bidirectional connection.
flight_edges = [
    ("Munich", "Vienna"),
    ("Istanbul", "Brussels"),
    ("Vienna", "Vilnius"),
    ("Madrid", "Munich"),
    ("Venice", "Brussels"),
    ("Riga", "Brussels"),
    ("Geneva", "Istanbul"),
    ("Munich", "Reykjavik"),
    ("Vienna", "Istanbul"),
    ("Riga", "Istanbul"),
    ("Reykjavik", "Vienna"),
    ("Venice", "Munich"),
    ("Madrid", "Venice"),
    ("Vilnius", "Istanbul"),
    ("Venice", "Vienna"),
    ("Venice", "Istanbul"),
    ("Reykjavik", "Madrid"),
    ("Riga", "Munich"),
    ("Munich", "Istanbul"),
    ("Reykjavik", "Brussels"),
    ("Vilnius", "Brussels"),
    ("Vilnius", "Munich"),  # from Vilnius to Munich (bidirectional assumed)
    ("Madrid", "Vienna"),
    ("Vienna", "Riga"),
    ("Geneva", "Vienna"),
    ("Madrid", "Brussels"),
    ("Vienna", "Brussels"),
    ("Geneva", "Brussels"),
    ("Geneva", "Madrid"),
    ("Munich", "Brussels"),
    ("Madrid", "Istanbul"),
    ("Geneva", "Munich"),
    ("Riga", "Vilnius")
]

# Build the flight graph as a dictionary mapping each city to a set of neighbors.
flight_graph = {}
for city1, city2 in flight_edges:
    for a, b in [(city1, city2), (city2, city1)]:
        if a not in flight_graph:
            flight_graph[a] = set()
        flight_graph[a].add(b)

# For our itinerary, we want an ordering of all 10 cities.
# To make sure the fixed time-window constraints work out well we force Geneva
# (visit relatives between day 1 and 4) to be at the beginning and Brussels
# (wedding between day 26 and 27) to be the last city.
fixed_first = "Geneva"
fixed_last = "Brussels"
remaining_cities = [city for city in durations.keys() if city not in (fixed_first, fixed_last)]

# The itinerary schedule is defined with overlapping flight days.
# The first city gets days 1...d1. Then for each subsequent city, if its duration is d,
# we assume the flight happens on the first day of its block (which is the last day of the previous block),
# so the new block contributes (d - 1) new days.
# Thus, if we denote the duration for each visited city in order as d1, d2, ..., dN,
# the total distinct days will be: d1 + (d2 - 1) + (d3 - 1) + ... + (dN - 1).
# For our required durations, the sum is:
#   total_days = durations[first] + sum(durations[city] - 1 for each subsequent city)
# Since sum(required durations) = 36, and there are 9 transitions,
# total distinct days = 36 - 9 = 27.
#
# Given an order, we can compute the day interval for each city as:
#   start_day[0] = 1, end_day[0] = 1 + d0 - 1 = d0.
#   For i > 0:
#       start_day[i] = end_day[i-1]   (flight day overlap)
#       end_day[i] = start_day[i] + durations[city_i] - 1.
#
# We then check that for cities with a time-window constraint,
# the interval [start_day, end_day] has a non-empty intersection with the specified window.
def compute_intervals(order):
    intervals = {}
    current_day = 1
    for city in order:
        d = durations[city]
        start = current_day
        end = current_day + d - 1
        intervals[city] = (start, end)
        # For next city, the flight day is the same as current city's end.
        current_day = end
    return intervals

def interval_intersects(interval, window):
    # interval and window are (start, end); we check if they have any day in common.
    a, b = interval
    L, U = window
    return not (b < L or a > U)

def valid_time_windows(intervals):
    # Check each city that has a time-window constraint.
    for city, window in time_windows.items():
        if city in intervals:
            if not interval_intersects(intervals[city], window):
                return False
    return True

def valid_flights(order):
    # Check that each consecutive pair in 'order' is connected by a direct flight.
    for i in range(len(order) - 1):
        a = order[i]
        b = order[i+1]
        if a not in flight_graph or b not in flight_graph[a]:
            return False
    return True

# Search over all permutations of the remaining cities.
# We fix the first city as fixed_first and the last city as fixed_last.
found_itinerary = None
for perm in itertools.permutations(remaining_cities):
    order = [fixed_first] + list(perm) + [fixed_last]
    if not valid_flights(order):
        continue
    intervals = compute_intervals(order)
    # The computed total distinct days is:
    total_days = sum(durations[order[0]] for _ in [0]) + sum(durations[city] - 1 for city in order[1:])
    # In our case total_days should be durations[order[0]] + sum(durations[city] - 1 for city in order[1:]) == 36 - 9 = 27.
    # (Since required durations sum to 36.)
    if total_days != 27:
        # This should always be 27 for the fixed durations.
        continue
    if not valid_time_windows(intervals):
        continue
    # If we reach here, we found a valid itinerary.
    found_itinerary = (order, intervals)
    break

# If no valid itinerary is found, we output an error.
if not found_itinerary:
    output = {"itinerary": "No valid itinerary found with the given constraints."}
else:
    order, intervals = found_itinerary
    # Build the itinerary in the desired JSON format.
    itinerary_list = []
    # We want a list of mappings each with a "day_range" and a "place".
    # Note: overlapping days occur at transitions.
    for city in order:
        start, end = intervals[city]
        day_range = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range, "place": city})
    output = {"itinerary": itinerary_list}

print(json.dumps(output))