#!/usr/bin/env python3
import itertools
import json
import sys

# Input constraints
total_days = 18

# Required days in each city
durations = {
    "Reykjavik": 4,
    "Riga": 2,
    "Oslo": 3,
    "Lyon": 5,
    "Dubrovnik": 2,
    "Madrid": 2,
    "Warsaw": 4,
    "London": 3
}

# Special date constraints:
# Riga: must be visited on a day that includes either day 4 or day 5.
riga_required_days = [4, 5]
# Dubrovnik: wedding between day 7 and day 8.
dubrovnik_required_days = [7, 8]

# Define flight connections.
# For most pairs, flights are bidirectional.
undirected_routes = [
    ("Warsaw", "Reykjavik"),
    ("Oslo", "Madrid"),
    ("Warsaw", "Riga"),
    ("Lyon", "London"),
    ("Madrid", "London"),
    ("Warsaw", "London"),
    ("Warsaw", "Oslo"),
    ("Oslo", "Dubrovnik"),
    ("Oslo", "Reykjavik"),
    ("Riga", "Oslo"),
    ("Oslo", "Lyon"),
    ("Oslo", "London"),
    ("London", "Reykjavik"),
    ("Warsaw", "Madrid"),
    ("Madrid", "Lyon"),
    ("Dubrovnik", "Madrid")
]

# Directed route: only from Reykjavik to Madrid.
directed_routes = [
    ("Reykjavik", "Madrid")
]

# Build the flight graph.
flights = {}
# Initialize nodes with empty sets.
for city in durations.keys():
    flights[city] = set()

# Add undirected routes (both directions)
for (a, b) in undirected_routes:
    flights[a].add(b)
    flights[b].add(a)

# Add directed routes (only one way)
for (a, b) in directed_routes:
    flights[a].add(b)
    # Do not add the reverse

# List of all cities
cities = list(durations.keys())

# Function to compute itinerary schedule given an ordering.
def compute_schedule(order):
    schedule = []
    current_day = 1
    for city in order:
        start = current_day
        d = durations[city]
        end = start + d - 1
        schedule.append((city, start, end))
        # Flight day: departure from this city and arrival at next is the same day (end day)
        current_day = end
    return schedule

# Check if the special date constraints are satisfied in the itinerary.
def meets_date_constraints(schedule):
    for city, start, end in schedule:
        if city == "Riga":
            # Must include day 4 or day 5.
            if not (start <= 4 <= end or start <= 5 <= end):
                return False
        if city == "Dubrovnik":
            # Must include day 7 or day 8.
            if not (start <= 7 <= end or start <= 8 <= end):
                return False
    return True

# Check if adjacent cities have a valid direct flight.
def valid_flight_connections(order):
    for i in range(len(order) - 1):
        origin = order[i]
        destination = order[i+1]
        if destination not in flights[origin]:
            return False
    return True

# Use backtracking / permutation search to find a valid itinerary.
found_schedule = None
for perm in itertools.permutations(cities):
    # Quick pruning: if Riga is first, its schedule (day 1-2) cannot include day4 or day5.
    if perm[0] == "Riga":
        continue
    # Likewise, if Dubrovnik is too early, it might not satisfy the wedding day constraint.
    # We'll check date constraints later.
    
    if not valid_flight_connections(perm):
        continue

    schedule = compute_schedule(perm)
    # The total days should be total_days; since sum(durations)-7==18, this should always hold.
    if schedule[-1][2] != total_days:
        continue

    if not meets_date_constraints(schedule):
        continue

    # Found a valid itinerary.
    found_schedule = schedule
    break

# Format the output itinerary.
itinerary_output = []
if found_schedule:
    for (city, start, end) in found_schedule:
        day_range = f"Day {start}-{end}"
        itinerary_output.append({"day_range": day_range, "place": city})

result = {"itinerary": itinerary_output}
print(json.dumps(result))
sys.exit(0)