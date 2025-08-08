#!/usr/bin/env python3
import itertools
import json

# Trip constraints
total_trip_days = 20

# Cities and required stay days
cities_info = {
    "Hamburg": 7,
    "Munich": 6,
    "Manchester": 2,
    "Lyon": 2,
    "Split": 7,
}

# Event constraints:
# - Attend annual show in Lyon between Day 13 and Day 14 
# - Visit relatives in Manchester between Day 19 and Day 20 (Manchester must be the final segment)

# Flight network (direct flights). For most pairs flights are bidirectional.
# Note: "from Manchester to Split" is only available in that direction,
# but our itinerary will have Manchester as the final stop so we won't use that edge.
flights = {
    "Hamburg": {"Manchester", "Munich", "Split"},
    "Munich": {"Hamburg", "Manchester", "Split", "Lyon"},
    "Manchester": {"Hamburg", "Munich", "Split"},  # directional: only Manchester->Split is allowed here.
    "Lyon": {"Split", "Munich"},
    "Split": {"Hamburg", "Munich", "Lyon"},
}

# The total required days summing the individual stays is 7+6+2+2+7 = 24.
# With 4 flight transitions (overlap days counted twice) we get 24 - 4 = 20 calendar days.
# Our itinerary segments will overlap on flight days.
#
# We define the itinerary as an ordered list of segments.
# For a given permutation order perm = [city0, city1, ..., city4] the calendar day boundaries are:
#   Segment[0]: days S0 to E0, with S0 = 1 and E0 = d(city0)
#   For i > 0: S[i] = E[i-1]  (flight day is the same for arrival and departure)
#             E[i] = S[i] + d(city_i) - 1
#
# We also need to satisfy the event constraints:
# - The segment for Lyon must exactly cover Day 13-14.
# - The Manchester segment (with 2 days) must cover Day 19-20.
#
# Given these constraints, Manchester must be the last city.
# And if Lyon is in the third segment (index 2), then S[2] = d(city0)+d(city1) - 1 must equal 13.
#
# We perform a simple search over permutations (with Manchester fixed at the end)
# that obey the available direct flights and event time constraints.

cities = list(cities_info.keys())
valid_itinerary = None

# Enumerate permutations and require Manchester to be the last city.
for perm in itertools.permutations(cities):
    if perm[-1] != "Manchester":
        continue

    # Check flight connectivity between consecutive cities.
    valid_flights = True
    for i in range(len(perm) - 1):
        origin = perm[i]
        destination = perm[i + 1]
        if destination not in flights.get(origin, set()):
            valid_flights = False
            break
    if not valid_flights:
        continue

    # Build the itinerary segments with overlapping flight days.
    segments = []
    current_day = 1
    for city in perm:
        duration = cities_info[city]
        start_day = current_day
        end_day = start_day + duration - 1
        segments.append((city, start_day, end_day))
        # If not the last segment, take a flight on the last day (overlap day)
        current_day = end_day

    # Verify the total trip duration.
    if segments[-1][2] != total_trip_days:
        continue

    # Enforce the Lyon event constraint.
    lyon_ok = True
    for city, s, e in segments:
        if city == "Lyon":
            if s != 13 or e != 14:
                lyon_ok = False
                break
    if not lyon_ok:
        continue

    # Enforce the Manchester relatives event constraint.
    # Since Manchester is the last city, it must cover days 19-20.
    if segments[-1][0] == "Manchester":
        if segments[-1][1] != 19 or segments[-1][2] != 20:
            continue

    # If all constraints are satisfied, we have found our itinerary.
    valid_itinerary = segments
    break

# Format the output in the required JSON structure.
if valid_itinerary is None:
    output = {"itinerary": []}
else:
    itinerary_list = []
    for city, start, end in valid_itinerary:
        itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
    output = {"itinerary": itinerary_list}

print(json.dumps(output))