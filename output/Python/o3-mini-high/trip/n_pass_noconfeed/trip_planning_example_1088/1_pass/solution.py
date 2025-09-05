#!/usr/bin/env python3
import itertools
import json

# Define the trip‐durations per city.
durations = {
    "Oslo": 5,
    "Stuttgart": 5,
    "Reykjavik": 2,
    "Split": 3,
    "Geneva": 2,
    "Porto": 3,
    "Tallinn": 5,
    "Stockholm": 3
}

# Define the direct flight connections.
# For most pairs the connection is assumed bidirectional.
flight_graph = {
    "Reykjavik": {"Stuttgart", "Stockholm", "Tallinn", "Oslo"},
    "Stockholm": {"Reykjavik", "Oslo", "Stuttgart", "Split", "Geneva"},
    "Stuttgart": {"Reykjavik", "Porto", "Stockholm", "Split"},
    "Tallinn": {"Reykjavik", "Oslo"},
    "Oslo": {"Reykjavik", "Stockholm", "Split", "Geneva", "Porto", "Tallinn"},
    "Split": {"Stockholm", "Stuttgart", "Oslo", "Geneva"},
    "Geneva": {"Stockholm", "Oslo", "Split", "Porto"},
    "Porto": {"Stuttgart", "Oslo", "Geneva"}
}

cities = ["Oslo", "Stuttgart", "Reykjavik", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]

# Event constraints:
# 1. You must attend a conference in Reykjavik on day 1 and day 2.
#    (So the Reykjavik stay must include days 1 and 2.)
# 2. You want to meet a friend in Stockholm between day 2 and day 4.
# 3. You must attend a workshop in Porto between day 19 and day 21.

# We note that because the flight‐rule is that if you fly on a day, you are present in both the departure and arrival cities,
# the overall trip (sum of durations minus number of flights) will equal 21 days.
# (Total durations = 28, and with 7 flights we get 28-7 = 21 days.)
#
# We will search over complete itineraries (orders of cities) that satisfy:
#   - The overall timeline (calculated by: start[0]=1, finish = start + duration - 1, and each subsequent
#     city starts on the finish day of the previous city) yields a total trip length of 21 days.
#   - Every consecutive pair of cities is connected by a direct flight per flight_graph.
#   - The conference constraint: The city "Reykjavik" (must be in the itinerary) has an interval that covers day 1-2.
#     (This almost forces Reykjavik to be first.)
#   - The friend meeting: The city "Stockholm" must be visited on at least one day between day 2 and day 4.
#   - The workshop: The city "Porto" must be visited on at least one day between day 19 and day 21.

# Because the conference in Reykjavik must be attended on day 1 and day 2,
# and the overlapping rule makes the very first city cover day 1,
# we will restrict our search to itineraries with "Reykjavik" as the first city.
#
# (Note: Similarly, to meet the Stockholm friend meeting window, Stockholm’s visitation interval
#  must intersect [2,4]. And for the workshop, Porto’s interval must intersect [19,21].)
#
# We perform a brute‐force search over all permutations of the other 7 cities.
# (There are 7! = 5040 possibilities.)

cities_except_rey = [c for c in cities if c != "Reykjavik"]

def compute_schedule(order):
    """
    Given an itinerary order (list of cities in order), compute a dictionary mapping 
    each city to its (start, finish) day.
    The rule is:
       start[0] = 1
       finish = start + duration - 1
       start[i+1] = finish[i]
    """
    schedule = {}
    start = 1
    for city in order:
        schedule[city] = (start, start + durations[city] - 1)
        start = start + durations[city] - 1
    return schedule

def intersects(interval, days_set):
    # Check if the set of days in interval (inclusive) intersects the given days_set.
    start, finish = interval
    days = set(range(start, finish + 1))
    return len(days.intersection(days_set)) > 0

def valid_flights(order):
    # Check direct flights for every consecutive pair.
    for i in range(len(order) - 1):
        a, b = order[i], order[i+1]
        # Assume flight connection is valid if b is in a's set or vice versa.
        if b not in flight_graph.get(a, set()) and a not in flight_graph.get(b, set()):
            return False
    return True

# We'll search for an itinerary that satisfies all constraints.
solution = None

# Enforce Reykjavik as first.
for perm in itertools.permutations(cities_except_rey):
    itinerary_order = ("Reykjavik",) + perm  # complete order of 8 cities
    schedule = compute_schedule(itinerary_order)
    
    # The overall trip length must be 21 days.
    # The finish day of the last city (by design) is sum(durations) - (num_flights)=28-7=21.
    if list(schedule.values())[-1][1] != 21:
        continue  # Should always be 21, but check for consistency.
    
    # Check flight connections
    if not valid_flights(itinerary_order):
        continue
    
    # Check Reykjavik conference: must cover day 1 and day 2.
    rey_interval = schedule["Reykjavik"]
    if not (rey_interval[0] <= 1 and rey_interval[1] >= 2):
        continue

    # Check friend meeting in Stockholm between day 2 and 4.
    if "Stockholm" not in schedule:
        continue
    stoc_interval = schedule["Stockholm"]
    if not intersects(stoc_interval, {2, 3, 4}):
        continue

    # Check workshop in Porto between day 19 and 21.
    if "Porto" not in schedule:
        continue
    porto_interval = schedule["Porto"]
    if not intersects(porto_interval, {19, 20, 21}):
        continue

    # If all constraints hold, we treat this itinerary as valid.
    solution = (itinerary_order, schedule)
    break

# Prepare the JSON output.
if solution is None:
    output = {"itinerary": []}
else:
    order, schedule = solution
    itinerary_list = []
    for city in order:
        start, finish = schedule[city]
        day_range = "Day {}-{}".format(start, finish)
        itinerary_list.append({"day_range": day_range, "place": city})
    output = {"itinerary": itinerary_list}

print(json.dumps(output))