#!/usr/bin/env python3
import json
import itertools

# Trip parameters: 8 cities, 25-day trip with overlapping flight days.
# Each city must be visited for a specified number of days.
durations = {
    "Vienna": 4,
    "Lyon": 3,
    "Edinburgh": 4,
    "Reykjavik": 5,
    "Stuttgart": 5,
    "Manchester": 2,
    "Split": 5,
    "Prague": 4
}

# The direct flight connections between cities (assumed bidirectional).
flights = {
    "Reykjavik": {"Stuttgart", "Vienna", "Prague"},
    "Stuttgart": {"Reykjavik", "Split", "Vienna", "Edinburgh", "Manchester"},
    "Split": {"Stuttgart", "Lyon", "Prague", "Manchester", "Vienna"},
    "Vienna": {"Stuttgart", "Manchester", "Lyon", "Prague", "Reykjavik", "Split"},
    "Prague": {"Manchester", "Edinburgh", "Vienna", "Split", "Lyon", "Reykjavik"},
    "Edinburgh": {"Prague", "Stuttgart"},
    "Manchester": {"Prague", "Split", "Stuttgart", "Vienna"},
    "Lyon": {"Vienna", "Split", "Prague"}
}

total_trip_days = 25
total_city_days = sum(durations.values())  # should be 32 (including overlap)
# Note: with 7 flight overlaps, calendar days = 32 - 7 = 25.

# Function to compute the schedule (list of tuples: (city, start_day, end_day))
def compute_schedule(itinerary):
    schedule = []
    # For segment 0, start at day 1.
    start_day = 1
    for city in itinerary:
        d = durations[city]
        # Each segment counts the first day also as a flight day (except the very first, which is just arrival)
        # So for segment i>0: current segment starts on the same day as the previous segment ended.
        end_day = start_day + d - 1
        schedule.append((city, start_day, end_day))
        # Next segment starts the same day as this segment's end (overlap flight day)
        start_day = end_day
    return schedule

# Constraint: Edinburgh must cover days 5-8 (i.e. show from day 5 to day 8 must be attended).
def satisfies_edinburgh(schedule):
    for city, start, end in schedule:
        if city == "Edinburgh":
            if start <= 5 and end >= 8:
                return True
            else:
                return False
    return True  # if Edinburgh not in schedule (should not happen)

# Constraint: Split visit must include at least one day in the window [19,23] (wedding)
def satisfies_split(schedule):
    for city, start, end in schedule:
        if city == "Split":
            # There is an overlap with [19,23] if start <= 23 and end >= 19.
            if start <= 23 and end >= 19:
                return True
            else:
                return False
    return True  # if Split not in schedule (should not happen)

# Check flight connectivity for consecutive cities.
def satisfies_flights(itinerary):
    for i in range(len(itinerary) - 1):
        curr_city = itinerary[i]
        next_city = itinerary[i+1]
        if next_city not in flights.get(curr_city, set()):
            return False
    return True

# We know by the temporal requirement that Edinburgh must cover days 5-8.
# A quick analysis shows that having Edinburgh as the 2nd segment forces:
#   segment0 must last exactly 5 days. Among cities with 5 days, Stuttgart, Reykjavik, Split qualify.
#   However, direct flights and the wedding constraint force us to choose Stuttgart for segment0.
# Also, from Edinburgh, the only direct flight available is to Prague.
# Hence, we fix the first three cities.
fixed_prefix = ["Stuttgart", "Edinburgh", "Prague"]

# The remaining cities to be scheduled.
all_cities = list(durations.keys())
remaining_cities = [city for city in all_cities if city not in fixed_prefix]

valid_itinerary = None

# Try all permutations of the remaining cities.
for perm in itertools.permutations(remaining_cities):
    candidate = fixed_prefix + list(perm)
    # Check flight connectivity for full itinerary.
    if not satisfies_flights(candidate):
        continue
    sched = compute_schedule(candidate)
    # Check Edinburgh show constraint.
    if not satisfies_edinburgh(sched):
        continue
    # Check Split wedding constraint.
    if not satisfies_split(sched):
        continue
    # The calendar day total should be 25.
    if sched[-1][2] != total_trip_days:
        continue
    valid_itinerary = sched
    break

# If a valid itinerary is found, prepare the JSON output.
output = {}
if valid_itinerary is not None:
    itinerary_list = []
    for city, start, end in valid_itinerary:
        day_range = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range, "place": city})
    output["itinerary"] = itinerary_list
else:
    output["itinerary"] = []

print(json.dumps(output))