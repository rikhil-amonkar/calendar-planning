#!/usr/bin/env python3
import json

# Input variables: durations (number of days to spend in each city)
durations = {
    "Oslo": 2,
    "Helsinki": 2,
    "Edinburgh": 3,
    "Riga": 2,
    "Tallinn": 5,
    "Budapest": 5,
    "Vilnius": 5,
    "Porto": 5,
    "Geneva": 4
}

# Flight graph.
# For flights of the form "CityA and CityB", we add bidirectional edges.
# For flights with "from X to Y", we add a directed edge.
flight_graph = {city: [] for city in durations.keys()}

def add_bidirectional(a, b):
    if b not in flight_graph[a]:
        flight_graph[a].append(b)
    if a not in flight_graph[b]:
        flight_graph[b].append(a)

def add_directed(src, dst):
    if dst not in flight_graph[src]:
        flight_graph[src].append(dst)

# Add flight connections based on the provided list:
# "Porto and Oslo"
add_bidirectional("Porto", "Oslo")
# "Edinburgh and Budapest"
add_bidirectional("Edinburgh", "Budapest")
# "Edinburgh and Geneva"
add_bidirectional("Edinburgh", "Geneva")
# "from Riga to Tallinn"
add_directed("Riga", "Tallinn")
# "Edinburgh and Porto"
add_bidirectional("Edinburgh", "Porto")
# "Vilnius and Helsinki"
add_bidirectional("Vilnius", "Helsinki")
# "from Tallinn to Vilnius"
add_directed("Tallinn", "Vilnius")
# "Riga and Oslo"
add_bidirectional("Riga", "Oslo")
# "Geneva and Oslo"
add_bidirectional("Geneva", "Oslo")
# "Edinburgh and Oslo"
add_bidirectional("Edinburgh", "Oslo")
# "Edinburgh and Helsinki"
add_bidirectional("Edinburgh", "Helsinki")
# "Vilnius and Oslo"
add_bidirectional("Vilnius", "Oslo")
# "Riga and Helsinki"
add_bidirectional("Riga", "Helsinki")
# "Budapest and Geneva"
add_bidirectional("Budapest", "Geneva")
# "Helsinki and Budapest"
add_bidirectional("Helsinki", "Budapest")
# "Helsinki and Oslo"
add_bidirectional("Helsinki", "Oslo")
# "Edinburgh and Riga"
add_bidirectional("Edinburgh", "Riga")
# "Tallinn and Helsinki"
add_bidirectional("Tallinn", "Helsinki")
# "Geneva and Porto"
add_bidirectional("Geneva", "Porto")
# "Budapest and Oslo"
add_bidirectional("Budapest", "Oslo")
# "Helsinki and Geneva"
add_bidirectional("Helsinki", "Geneva")
# "from Riga to Vilnius"
add_directed("Riga", "Vilnius")
# "Tallinn and Oslo"
add_bidirectional("Tallinn", "Oslo")

# Total trip days is 25.
total_trip_days = 25

# We must visit 9 cities. Additionally, the constraints state:
# - 2 days in Oslo and meeting a friend there between day 24 and 25.
# - 2 days in Helsinki.
# - 3 days in Edinburgh.
# - 2 days in Riga.
# - 5 days in Tallinn (with a wedding in Tallinn between day 4 and 8).
# - 5 days in Budapest.
# - 5 days in Vilnius.
# - 5 days in Porto.
# - 4 days in Geneva.
#
# The sum of the durations is 33, and because if you fly from one city
# to the next on a same calendar day this day counts for both cities,
# there will be 8 overlapping flight days. Thus the total is 33 - 8 = 25.
#
# In addition, we require that the meeting in Oslo is at the end of the itinerary,
# i.e. Oslo is visited last (with its start day either 23 or 24)
# and that Tallinn’s visit (wedding) must include some day between 4 and 8.
#
# To simplify, we force Oslo to be the final city.
cities_except_oslo = [city for city in durations if city != "Oslo"]

# Helper function: given an ordering (list of cities), compute the start day for each city.
# The rule is:
#   start_day[0] = 1
#   For i > 0, start_day[i] = start_day[i-1] + durations[order[i-1]] - 1
def compute_start_days(order):
    start_days = []
    current = 1
    for city in order:
        start_days.append(current)
        current = current + durations[city] - 1
    return start_days

# We will use backtracking to try to find an ordering (permutation) of the 8 cities (excluding Oslo)
# such that consecutive cities are connected by a direct flight, and the scheduling constraints hold.
# In the final complete itinerary, we append "Oslo" as the last city and also require a direct flight
# from the last chosen city to "Oslo". Additionally, we require that:
#   - If "Tallinn" appears, its start day <= 8 (so that the wedding day window [4,8] is included).
#   - For "Oslo" (duration=2), its start day (when appended last) must be either 23 or 24 
#     so that the friend meeting (on day 24/25) is satisfied.
solution_found = [False]   # mutable flag
final_order_solution = []
final_start_solution = []

def backtrack(order):
    global solution_found, final_order_solution, final_start_solution
    if solution_found[0]:
        return
    if len(order) == len(cities_except_oslo):
        # Check connectivity from the last city to "Oslo"
        last = order[-1]
        if "Oslo" not in flight_graph.get(last, []):
            return
        # Compute start days for the current order
        partial_starts = compute_start_days(order)
        # Compute Oslo's start day when appended at the end.
        # For the complete itinerary, order_complete = order + ["Oslo"]
        # Oslo_start = last_city_start + durations[last] - 1.
        oslo_start = partial_starts[-1] + (durations[last] - 1)
        if oslo_start not in [23, 24]:
            return
        # Form the complete order and start days.
        complete_order = order + ["Oslo"]
        complete_starts = compute_start_days(complete_order)
        # Check that Tallinn's wedding window is satisfied.
        # For every occurrence of Tallinn, its visit window is [start, start+durations - 1]
        # and we require that it overlaps with [4,8].
        for idx, city in enumerate(complete_order):
            if city == "Tallinn":
                start_day = complete_starts[idx]
                end_day = start_day + durations[city] - 1
                # Check for overlap with [4,8]: valid if not (end_day < 4 or start_day > 8)
                if end_day < 4 or start_day > 8:
                    return
        # All constraints satisfied; record solution.
        solution_found[0] = True
        final_order_solution = complete_order
        final_start_solution = complete_starts
        return

    # Try each city not yet in order
    for candidate in cities_except_oslo:
        if candidate in order:
            continue
        # If order is not empty, check flight connectivity from last city to candidate.
        if order:
            last_city = order[-1]
            if candidate not in flight_graph.get(last_city, []):
                continue
        # Compute new order's start days.
        new_order = order + [candidate]
        start_days = compute_start_days(new_order)
        # If the candidate is Tallinn, ensure its start day is <= 8.
        if candidate == "Tallinn" and start_days[-1] > 8:
            continue
        # Continue recursion.
        backtrack(new_order)
        if solution_found[0]:
            return

# Start backtracking with an empty order.
backtrack([])

# If no solution is found, we will output an empty itinerary.
itinerary = []
if final_order_solution:
    # Build itinerary segments: for each city, determine the day range.
    segments = []
    for idx, city in enumerate(final_order_solution):
        start_day = final_start_solution[idx]
        end_day = start_day + durations[city] - 1
        segment = {"day_range": f"Day {start_day}-{end_day}", "place": city}
        segments.append(segment)
    itinerary = segments

# Output the result as a JSON-formatted dictionary.
result = {"itinerary": itinerary}
print(json.dumps(result))