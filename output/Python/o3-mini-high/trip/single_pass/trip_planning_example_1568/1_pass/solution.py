#!/usr/bin/env python3
import json
import itertools

# Define the flight network as an undirected graph.
# Each tuple represents a direct flight between two cities.
flights = [
    ("Riga", "Stockholm"),
    ("Stockholm", "Brussels"),
    ("Istanbul", "Munich"),
    ("Istanbul", "Riga"),
    ("Prague", "Split"),
    ("Vienna", "Brussels"),
    ("Vienna", "Riga"),
    ("Split", "Stockholm"),
    ("Munich", "Amsterdam"),
    ("Split", "Amsterdam"),
    ("Amsterdam", "Stockholm"),
    ("Amsterdam", "Riga"),
    ("Vienna", "Stockholm"),
    ("Vienna", "Istanbul"),
    ("Vienna", "Seville"),
    ("Istanbul", "Amsterdam"),
    ("Munich", "Brussels"),
    ("Prague", "Munich"),
    ("Riga", "Munich"),
    ("Prague", "Amsterdam"),
    ("Prague", "Brussels"),
    ("Prague", "Istanbul"),
    ("Istanbul", "Stockholm"),
    ("Vienna", "Prague"),
    ("Munich", "Split"),
    ("Vienna", "Amsterdam"),
    ("Prague", "Stockholm"),
    ("Brussels", "Seville"),
    ("Munich", "Stockholm"),
    ("Istanbul", "Brussels"),
    ("Amsterdam", "Seville"),
    ("Vienna", "Split"),
    ("Munich", "Seville"),
    ("Riga", "Brussels"),
    ("Prague", "Riga"),
    ("Vienna", "Munich")
]
# Build the graph as a dictionary of sets.
graph = {}
for a, b in flights:
    graph.setdefault(a, set()).add(b)
    graph.setdefault(b, set()).add(a)

# Define required durations for each city.
durations = {
    "Vienna": 5,
    "Prague": 5,
    "Amsterdam": 3,
    "Split": 3,
    "Munich": 2,
    "Seville": 3,
    "Istanbul": 2,
    "Brussels": 2,
    "Riga": 2,
    "Stockholm": 2
}

# Define fixed interval constraints for some cities.
# They must appear with exactly these calendar day spans.
fixed_intervals = {
    "Vienna": (1, 5),         # friend meeting between day 1 and day 5
    "Prague": (5, 9),         # annual show from day 5 to day 9 must occur in Prague
    "Split": (11, 13),        # relatives in Split between day 11 and 13
    "Riga": (15, 16),         # meet friends in Riga between day 15 and 16
    "Stockholm": (16, 17)     # conference in Stockholm during day 16 and 17
}

# Fixed positions for cities with predetermined calendar dates:
# Vienna must be day 1-5, Prague 5-9, and Split 11-13.
# Also, from Prague it is necessary to transit by a 3-day city that is reachable;
# among the free 3-day options (Amsterdam and Seville), Prague->Amsterdam is available.
fixed_first4 = ["Vienna", "Prague", "Amsterdam", "Split"]

# The remaining cities to assign (positions 5 to 10) are:
remaining_cities = {"Munich", "Seville", "Istanbul", "Brussels", "Riga", "Stockholm"}

# A helper function to compute the itinerary intervals given an ordered list of cities.
# We use the rule: s1 = 1; for each city at position i, start = T_{i-1} and finish = start + duration - 1.
def compute_intervals(itinerary, durations):
    intervals = []
    current_day = 1
    for city in itinerary:
        start = current_day
        finish = start + durations[city] - 1
        intervals.append((start, finish))
        # Next city starts on the same day when flight happens.
        current_day = finish
    return intervals

# Check if the computed interval for a city must match a fixed interval if one is given.
def check_fixed_intervals(itinerary, intervals, fixed_intervals):
    # For each city with a fixed interval constraint, its computed (start, finish)
    # must exactly equal the fixed tuple.
    for i, city in enumerate(itinerary):
        if city in fixed_intervals:
            if intervals[i] != fixed_intervals[city]:
                return False
    return True

# Check flight connectivity between consecutive cities in the itinerary.
def check_connectivity(itinerary, graph):
    for i in range(len(itinerary)-1):
        a = itinerary[i]
        b = itinerary[i+1]
        if b not in graph.get(a, set()):
            return False
    return True

# Total trip must finish on day 20.
def check_total_duration(intervals):
    return intervals[-1][1] == 20

# Now we need to build the complete itinerary.
# The first four positions are fixed.
first_part = fixed_first4

# We'll try all permutations for the remaining six cities.
valid_itinerary = None
for perm in itertools.permutations(remaining_cities):
    candidate = first_part + list(perm)
    # Compute the intervals.
    intervals = compute_intervals(candidate, durations)
    # Check total trip duration requirement.
    if not check_total_duration(intervals):
        continue
    # Check fixed interval constraints.
    if not check_fixed_intervals(candidate, intervals, fixed_intervals):
        continue
    # Check flight connectivity for the full itinerary.
    if not check_connectivity(candidate, graph):
        continue
    # If all constraints are met, select this itinerary.
    valid_itinerary = (candidate, intervals)
    break

# If a valid itinerary was found, format the result.
if valid_itinerary:
    itinerary_order, intervals = valid_itinerary
    output = {"itinerary": []}
    for city, (start, finish) in zip(itinerary_order, intervals):
        day_range = f"Day {start}-{finish}"
        output["itinerary"].append({"day_range": day_range, "place": city})
else:
    output = {"itinerary": [], "error": "No valid itinerary found."}

# Output the result as JSON.
print(json.dumps(output))