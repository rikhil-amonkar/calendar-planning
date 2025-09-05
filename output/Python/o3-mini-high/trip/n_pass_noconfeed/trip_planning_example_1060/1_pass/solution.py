#!/usr/bin/env python3
import json
import itertools

# Trip constraints and city durations (in "city-days" including overlap on flight days)
# The total sum of durations is 32 and with 7 overlapping flight days, total trip length is 25 days.
durations = {
    "Reykjavik": 4,   # Must include a workshop between day 1 and 4.
    "Stuttgart": 4,   # Must include a conference on day 4 and day 7.
    "Valencia": 5,
    "Seville": 3,
    "Munich": 3,      # Annual show from day 13 to day 15 (so Munich segment must be exactly day 13-15).
    "Geneva": 5,
    "Istanbul": 4,    # Visit relatives between day 19 and day 22 (so Istanbul segment must be day 19-22).
    "Vilnius": 4
}

# List of allowed cities
cities = list(durations.keys())

# Build the flight network. Some flights are undirected and some are directed.
# Directed edges are added only in one direction.
graph = {city: set() for city in cities}

# Directed flights
directed_flights = [
    ("Reykjavik", "Stuttgart"),  # only from Reykjavik to Stuttgart
    ("Vilnius", "Munich")         # only from Vilnius to Munich
]

# Undirected flights (add both directions)
undirected_flights = [
    ("Geneva", "Istanbul"),
    ("Reykjavik", "Munich"),
    ("Stuttgart", "Valencia"),
    ("Stuttgart", "Istanbul"),
    ("Munich", "Geneva"),
    ("Istanbul", "Vilnius"),
    ("Valencia", "Seville"),
    ("Valencia", "Istanbul"),
    ("Seville", "Munich"),
    ("Munich", "Istanbul"),
    ("Valencia", "Geneva"),
    ("Valencia", "Munich")
]

# Add directed flights
for origin, dest in directed_flights:
    graph[origin].add(dest)

# Add undirected flights (both directions)
for a, b in undirected_flights:
    graph[a].add(b)
    graph[b].add(a)

# We must take a route that visits all 8 cities exactly once
# and only uses given direct flights.
#
# Also, due to special constraints on workshop, conference, show and relatives, 
# we choose to fix some positions in the itinerary timeline:
#   - "Reykjavik" must be visited first (to cover the workshop between day 1 and 4)
#   - "Stuttgart" must come second so that its 4-day block (Day 4-7) contains day 4 and day 7.
#   - "Munich" must appear in the 5th segment to exactly cover day 13-15.
#   - "Istanbul" must appear in the 7th segment to cover day 19-22.
#
# Positions: index0, index1, index2, index3, index4, index5, index6, index7.
fixed_positions = {
    0: "Reykjavik",
    1: "Stuttgart",
    4: "Munich",
    6: "Istanbul"
}

# The remaining positions should be filled with the remaining cities.
remaining_cities = set(cities) - set(fixed_positions.values())
remaining_positions = [i for i in range(8) if i not in fixed_positions]

# Function to compute the itinerary timeline based on an ordering.
# On a flight day, the day is counted for both the departing and arriving city.
def compute_timeline(order):
    # order: list of 8 cities in the itinerary order.
    # The first segment starts on Day 1.
    timeline = []
    current_day = 1
    for city in order:
        start_day = current_day
        end_day = start_day + durations[city] - 1
        timeline.append((start_day, end_day))
        # Flight day overlap: next segment starts on the same day as the previous segment's end.
        current_day = end_day
    return timeline

# Function to check timeline constraints for special events.
def check_timeline_constraints(order, timeline):
    for city, (start, end) in zip(order, timeline):
        if city == "Reykjavik":
            # Workshop must be attended between Day 1 and Day 4.
            # For the first city, if it starts on 1 and has 4 days, it covers days 1-4.
            if not (start <= 1 and end >= 4):
                return False
        if city == "Stuttgart":
            # Conference on Day 4 and Day 7 must be attended in Stuttgart.
            if not (start <= 4 <= end and start <= 7 <= end):
                return False
        if city == "Munich":
            # Annual show in Munich from Day 13 to Day 15
            if not (start == 13 and end == 15):
                return False
        if city == "Istanbul":
            # Visit relatives in Istanbul between Day 19 and Day 22.
            if not (start == 19 and end == 22):
                return False
    # Check if the final day equals 25.
    if timeline[-1][1] != 25:
        return False
    return True

# Function to check flight connectivity for the ordering.
def check_flights(order):
    for i in range(len(order) - 1):
        current_city = order[i]
        next_city = order[i+1]
        if next_city not in graph[current_city]:
            return False
    return True

# Now, use backtracking (via permutation of the remaining cities in the remaining positions) 
# to find an ordering that satisfies:
#   1. The fixed positions are met.
#   2. Flight connectivity between consecutive cities.
#   3. Timeline constraints for special events.
all_positions = [None] * 8
for pos, city in fixed_positions.items():
    all_positions[pos] = city

valid_order = None

# Try all permutations of remaining cities for the free positions.
for perm in itertools.permutations(remaining_cities, len(remaining_positions)):
    candidate = all_positions.copy()
    for idx, pos in enumerate(remaining_positions):
        candidate[pos] = perm[idx]
    # Check flight connectivity:
    if not check_flights(candidate):
        continue
    timeline = compute_timeline(candidate)
    if not check_timeline_constraints(candidate, timeline):
        continue
    valid_order = candidate
    valid_timeline = timeline
    break

if not valid_order:
    result = {"itinerary": []}
else:
    # Build the itinerary list with day_range and place using the computed timeline.
    itinerary = []
    for city, (start, end) in zip(valid_order, valid_timeline):
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    result = {"itinerary": itinerary}

# Output the result as JSON
print(json.dumps(result))