#!/usr/bin/env python3
import itertools
import json

# Fixed durations (in days, as given)
durations = {
    "Prague": 5,
    "Tallinn": 3,
    "Warsaw": 2,
    "Porto": 3,
    "Naples": 5,
    "Milan": 3,
    "Lisbon": 5,
    "Santorini": 5,
    "Riga": 4,
    "Stockholm": 2
}

# Construct allowed flight connections.
# For bidirectional flights, both directions will be added.
allowed_flights = set()

def add_bidirectional(a, b):
    allowed_flights.add((a, b))
    allowed_flights.add((b, a))
    
def add_oneway(a, b):
    allowed_flights.add((a, b))

# Parse the connections as given in the problem statement:
add_bidirectional("Riga", "Prague")                   # Riga and Prague
add_bidirectional("Stockholm", "Milan")                # Stockholm and Milan
add_bidirectional("Riga", "Milan")                     # Riga and Milan
add_bidirectional("Lisbon", "Stockholm")               # Lisbon and Stockholm
add_oneway("Stockholm", "Santorini")                   # from Stockholm to Santorini
add_bidirectional("Naples", "Warsaw")                  # Naples and Warsaw
add_bidirectional("Lisbon", "Warsaw")                  # Lisbon and Warsaw
add_bidirectional("Naples", "Milan")                   # Naples and Milan
add_bidirectional("Lisbon", "Naples")                  # Lisbon and Naples
add_oneway("Riga", "Tallinn")                          # from Riga to Tallinn
add_bidirectional("Tallinn", "Prague")                 # Tallinn and Prague
add_bidirectional("Stockholm", "Warsaw")               # Stockholm and Warsaw
add_bidirectional("Riga", "Warsaw")                    # Riga and Warsaw
add_bidirectional("Lisbon", "Riga")                    # Lisbon and Riga
add_bidirectional("Riga", "Stockholm")                # Riga and Stockholm
add_bidirectional("Lisbon", "Porto")                   # Lisbon and Porto
add_bidirectional("Lisbon", "Prague")                  # Lisbon and Prague
add_bidirectional("Milan", "Porto")                    # Milan and Porto
add_bidirectional("Prague", "Milan")                   # Prague and Milan
add_bidirectional("Lisbon", "Milan")                   # Lisbon and Milan
add_bidirectional("Warsaw", "Porto")                   # Warsaw and Porto
add_bidirectional("Warsaw", "Tallinn")                 # Warsaw and Tallinn
add_bidirectional("Santorini", "Milan")                # Santorini and Milan
add_bidirectional("Stockholm", "Prague")               # Stockholm and Prague
add_bidirectional("Stockholm", "Tallinn")              # Stockholm and Tallinn
add_bidirectional("Warsaw", "Milan")                   # Warsaw and Milan (duplicate ok)
add_bidirectional("Santorini", "Naples")               # Santorini and Naples
add_bidirectional("Warsaw", "Prague")                  # Warsaw and Prague

# The itinerary must visit all 10 cities.
# In addition to the event constraints below:
#  - Riga must host the annual show from Day 5 to Day 8.
#    (This forces the schedule: if flown on day X from city A to city B,
#     then B’s start day equals A’s end day. In particular, to have Riga’s
#     stay be Day 5-8 we require Riga to be in position 2 and city1 to last 5 days.)
#  - You want to spend 5 days in Prague.
#  - You plan to visit Tallinn for 3 days and must be there (or a part thereof)
#    on one day between Day 18 and Day 20.
#  - You plan to stay in Warsaw for 2 days.
#  - You want to spend 3 days in Porto.
#  - You plan to visit Naples for 5 days.
#  - You plan to stay in Milan for 3 days and must be there on a day between Day 24 and Day 26.
#  - You would like to visit Lisbon for 5 days.
#  - You plan to stay in Santorini for 5 days.
#  - You would like to visit Stockholm for 2 days.
#
# Note on transitions: if you fly out on day X, you count that day in both cities.

# We fix that the itinerary MUST start with "Prague" (5 days) and second must be "Riga" (4 days)
# so that Riga's start day becomes day 5 (since S[1]=1 and E[1]=5, then S[2]=5).
fixed_order = ["Prague", "Riga"]

# The remaining cities to order:
remaining = ["Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Stockholm"]

# We'll search over all permutations of the remaining 8 cities.
def compute_schedule(order):
    # Given full order list, compute (start, end) for each visited city.
    schedule = []
    current_start = 1
    for city in order:
        d = durations[city]
        current_end = current_start + d - 1  # inclusive end day
        schedule.append((current_start, current_end))
        # Transition: if flight from A to B on same day X, then B's start day = current_end.
        current_start = current_end
    return schedule

def interval_intersects(start, end, target_start, target_end):
    # Returns True if the interval [start, end] (inclusive) intersects [target_start, target_end]
    return not (end < target_start or start > target_end)

def meets_event_constraints(full_order, schedule):
    # full_order: list of city names in visit order.
    # schedule: list of (start, end) for each city.
    for city, (s, e) in zip(full_order, schedule):
        if city == "Riga":
            # Riga must be exactly day 5 to day 8.
            if s != 5 or e != 8:
                return False
        if city == "Tallinn":
            # Must have at least one day between 18 and 20 (inclusive)
            if not interval_intersects(s, e, 18, 20):
                return False
        if city == "Milan":
            # Must have at least one day between 24 and 26 (inclusive)
            if not interval_intersects(s, e, 24, 26):
                return False
    return True

def flights_ok(full_order):
    # For each consecutive pair, check if a direct flight exists (taking directional restrictions into account)
    for i in range(len(full_order) - 1):
        a = full_order[i]
        b = full_order[i+1]
        if (a, b) not in allowed_flights:
            return False
    return True

# The total itinerary must be exactly 28 days.
def total_itinerary_days(schedule):
    # The end day of the last city is the total itinerary length.
    return schedule[-1][1]

solution = None

# Iterate over all permutations of the 8 remaining cities.
for perm in itertools.permutations(remaining):
    full_order = fixed_order + list(perm)
    sched = compute_schedule(full_order)
    # Check that overall itinerary length equals 28 days.
    if total_itinerary_days(sched) != 28:
        continue
    if not meets_event_constraints(full_order, sched):
        continue
    if not flights_ok(full_order):
        continue
    # Found a valid itinerary.
    solution = (full_order, sched)
    break

if solution is None:
    result = {"itinerary": []}
else:
    order, sched = solution
    itinerary = []
    for city, (s, e) in zip(order, sched):
        day_range = "Day {}-{}".format(s, e)
        itinerary.append({"day_range": day_range, "place": city})
    result = {"itinerary": itinerary}

# Output valid JSON
print(json.dumps(result))