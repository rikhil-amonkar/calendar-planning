#!/usr/bin/env python3
import itertools
import json

# Define flight connections as a set of frozensets (bidirectional)
flights = {
    frozenset(["Venice", "Stuttgart"]),
    frozenset(["Oslo", "Brussels"]),
    frozenset(["Split", "Copenhagen"]),
    frozenset(["Barcelona", "Copenhagen"]),
    frozenset(["Barcelona", "Venice"]),
    frozenset(["Brussels", "Venice"]),
    frozenset(["Barcelona", "Stuttgart"]),
    frozenset(["Copenhagen", "Brussels"]),
    frozenset(["Oslo", "Split"]),
    frozenset(["Oslo", "Venice"]),
    frozenset(["Barcelona", "Split"]),
    frozenset(["Oslo", "Copenhagen"]),
    frozenset(["Barcelona", "Oslo"]),
    frozenset(["Copenhagen", "Stuttgart"]),
    frozenset(["Split", "Stuttgart"]),
    frozenset(["Copenhagen", "Venice"]),
    frozenset(["Barcelona", "Brussels"])
}

# Define city info with required duration and any specific constraints.
# Constraints that require a meeting (or attendance) are defined as a tuple (earliest, latest).
city_info = {
    "Barcelona": {"duration": 3, "constraint": {"show": (1, 3)}},  # must attend show from Day 1 to Day 3
    "Oslo": {"duration": 2, "constraint": {"friend": (3, 4)}},       # meet friend in Oslo between Day 3 and Day 4
    "Stuttgart": {"duration": 3},
    "Venice": {"duration": 4},
    "Split": {"duration": 4},
    "Brussels": {"duration": 3, "constraint": {"friend": (9, 11)}},   # meet friend in Brussels between Day 9 and Day 11
    "Copenhagen": {"duration": 3}
}

# The overall itinerary will have 7 cities and must exactly cover 16 calendar days.
# Note: if you fly from city A to city B on day X, then day X is counted for both cities.
# Total city-days = sum(durations) = 22, and with 6 transitions (overlaps) we have 22 - 6 = 16 days.

# We fix the first two cities based on non-negotiable constraints:
# Barcelona must be first (because of the annual show from Day 1 to Day 3)
# Oslo must follow to satisfy the friend meeting between Day 3 and Day 4.
fixed_order = ["Barcelona", "Oslo"]

# Remaining cities to schedule (order to be determined)
remaining_cities = ["Stuttgart", "Venice", "Split", "Brussels", "Copenhagen"]

def is_connected(city_a, city_b):
    return frozenset([city_a, city_b]) in flights

def timeline_for_itinerary(itinerary):
    # Compute timeline given an itinerary order.
    # The first city starts on Day 1.
    timeline = []
    start_day = 1
    for city in itinerary:
        duration = city_info[city]["duration"]
        end_day = start_day + duration - 1  # city is visited on days start_day ... end_day
        timeline.append({"place": city, "start": start_day, "end": end_day})
        # Flight from city to the next: depart on end_day, which is counted in both cities.
        start_day = end_day
    return timeline

def meets_time_window(segment, window):
    # segment has "start" and "end"; window is a tuple (earliest, latest).
    # We require that the segment's period [start, end] intersects with [window[0], window[1]].
    return segment["start"] <= window[1] and segment["end"] >= window[0]

# Search for a valid itinerary order among the remaining cities.
valid_itinerary = None
for perm in itertools.permutations(remaining_cities):
    full_order = fixed_order + list(perm)
    # Check that every consecutive flight connection is available.
    valid_connection = True
    for i in range(len(full_order) - 1):
        if not is_connected(full_order[i], full_order[i+1]):
            valid_connection = False
            break
    if not valid_connection:
        continue

    # Compute the timeline (day ranges) for each city in the itinerary.
    timeline = timeline_for_itinerary(full_order)
    # Check that the final city ends exactly on Day 16.
    if timeline[-1]["end"] != 16:
        continue

    # Check specific city constraints:
    constraints_satisfied = True
    for segment in timeline:
        city = segment["place"]
        if "constraint" in city_info[city]:
            for key, window in city_info[city]["constraint"].items():
                # For the cities with time-bound meetings/attendance, check that at least one day in the segment falls within the required window.
                if not meets_time_window(segment, window):
                    constraints_satisfied = False
                    break
        if not constraints_satisfied:
            break

    if constraints_satisfied:
        valid_itinerary = timeline
        break

if valid_itinerary is None:
    output = {"itinerary": [], "error": "No valid itinerary found."}
else:
    # Prepare the itinerary in the requested JSON format.
    itinerary_list = []
    for seg in valid_itinerary:
        day_range = f"Day {seg['start']}-{seg['end']}"
        itinerary_list.append({"day_range": day_range, "place": seg["place"]})
    output = {"itinerary": itinerary_list}

print(json.dumps(output))