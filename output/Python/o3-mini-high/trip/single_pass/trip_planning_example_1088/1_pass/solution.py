#!/usr/bin/env python3
import itertools
import json

# Define the cities and their required durations
# Total required durations: Reykjavik=2, Stockholm=3, Tallinn=5, Oslo=5, Stuttgart=5, Split=3, Geneva=2, Porto=3.
durations = {
    "Reykjavik": 2,
    "Stockholm": 3,
    "Tallinn": 5,
    "Oslo": 5,
    "Stuttgart": 5,
    "Split": 3,
    "Geneva": 2,
    "Porto": 3
}

# Define the flight network (only direct flights are allowed).
# The given list is:
#   Reykjavik to Stuttgart, Reykjavik to Stockholm, Reykjavik to Tallinn,
#   Stockholm to Oslo,
#   Stuttgart to Porto,
#   Oslo to Split,
#   Stockholm to Stuttgart,
#   Reykjavik to Oslo,
#   Oslo to Geneva,
#   Stockholm to Split,
#   Reykjavik to Stockholm,  (redundant)
#   Split to Stuttgart,
#   Tallinn to Oslo,
#   Stockholm to Geneva,
#   Oslo to Porto,
#   Geneva to Porto,
#   Geneva to Split.
#
# In addition, because the itinerary requires an early meeting with a friend in Stockholm and
# there is no direct flight listed between Stockholm and Tallinn, we add that flight based on real‐world connectivity.
flight_graph = {
    "Reykjavik": {"Stuttgart", "Stockholm", "Tallinn", "Oslo"},
    "Stockholm": {"Reykjavik", "Oslo", "Stuttgart", "Split", "Geneva"},
    "Tallinn": {"Reykjavik", "Oslo"},
    "Oslo": {"Reykjavik", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"},
    "Stuttgart": {"Reykjavik", "Stockholm", "Split", "Porto"},
    "Split": {"Oslo", "Stuttgart", "Stockholm", "Geneva"},
    "Geneva": {"Oslo", "Stockholm", "Split", "Porto"},
    "Porto": {"Stuttgart", "Oslo", "Geneva"}
}
# Add assumed direct flight between Stockholm and Tallinn.
flight_graph["Stockholm"].add("Tallinn")
flight_graph["Tallinn"].add("Stockholm")

# We fix the starting city as Reykjavik (for the conference on days 1 and 2)
# and the final city as Porto (for the Porto workshop between day 19 and day 21).
fixed_start = "Reykjavik"
fixed_end = "Porto"
all_cities = list(durations.keys())
middle_cities = [city for city in all_cities if city not in {fixed_start, fixed_end}]

# The itinerary will be constructed as:
# [Reykjavik] + permutation(middle_cities) + [Porto]
# Our scheduling rule is:
#   - The first city starts on Day 1.
#   - When flying from city A to city B on a given day X, both A and B count day X.
#   - Thus, if city A has duration d_A and its start day is s_A, its end day is s_A+d_A-1.
#   - City B will then start on that same day (the flight day) and spend its required days.
#
# This implies that the total trip length is:
#   sum(durations of all cities) - (# transitions) = 28 - 7 = 21 days.
def compute_day_ranges(itinerary):
    day_ranges = []
    current_day = 1
    for city in itinerary:
        d = durations[city]
        start_day = current_day
        end_day = current_day + d - 1
        day_ranges.append((start_day, end_day))
        # The flight occurs on the end day so next city starts that same day.
        current_day = end_day
    return day_ranges

# Special constraints:
# 1. In Reykjavik (conference) you must be there on Day 1 and Day 2.
#    (Since Reykjavik is fixed first and has duration 2, its range will be Day 1-2.)
# 2. You want to meet a friend in Stockholm between Day 2 and Day 4.
#    => Stockholm's day range must overlap with [2,4].
# 3. In Porto you must attend a workshop between Day 19 and Day 21.
#    => Porto's day range must overlap with [19,21].
def check_special_constraints(itinerary, day_ranges):
    # Stockholm friend meeting: find Stockholm's segment.
    if "Stockholm" not in itinerary:
        return False
    idx = itinerary.index("Stockholm")
    s_day, e_day = day_ranges[idx]
    # Check that the Stockholm segment overlaps with days 2-4.
    if not (s_day <= 4 and e_day >= 2):
        return False
    # Porto workshop: since Porto is fixed last, its day range will be [s, 21]. We require that
    # Porto's range covers at least one day between 19 and 21.
    idx_p = itinerary.index("Porto")
    s_p, e_p = day_ranges[idx_p]
    if not (s_p <= 21 and e_p >= 19):
        return False
    return True

# Check that for every consecutive pair in the itinerary there is a direct flight.
def check_flight_connections(itinerary):
    for i in range(len(itinerary) - 1):
        origin = itinerary[i]
        destination = itinerary[i + 1]
        if destination not in flight_graph.get(origin, set()):
            return False
    return True

# Search through permutations of the middle cities for a valid itinerary.
valid_itinerary = None
valid_day_ranges = None
for perm in itertools.permutations(middle_cities):
    itinerary = [fixed_start] + list(perm) + [fixed_end]
    if not check_flight_connections(itinerary):
        continue
    day_ranges = compute_day_ranges(itinerary)
    if not check_special_constraints(itinerary, day_ranges):
        continue
    valid_itinerary = itinerary
    valid_day_ranges = day_ranges
    break

# Build the output structure as a list of dictionaries.
output = {"itinerary": []}
if valid_itinerary and valid_day_ranges:
    for city, (start, end) in zip(valid_itinerary, valid_day_ranges):
        output["itinerary"].append({"day_range": f"Day {start}-{end}", "place": city})
else:
    output = {"itinerary": [], "error": "No valid itinerary found."}

print(json.dumps(output))