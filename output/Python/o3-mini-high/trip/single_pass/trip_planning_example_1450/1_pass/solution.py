#!/usr/bin/env python3
import json

# Trip constraints and parameters
# Cities with required durations (days)
cities = {
    "Stockholm": 3,
    "Hamburg": 5,
    "Florence": 2,
    "Istanbul": 5,
    "Oslo": 5,
    "Vilnius": 5,
    "Santorini": 2,
    "Munich": 5,
    "Frankfurt": 4,
    "Krakow": 5
}

# Total unique trip days = sum(durations) - (#transitions)
TOTAL_UNIQUE_DAYS = sum(cities.values()) - (len(cities) - 1)  # 41 - 9 = 32

# Flight connections as given (we treat them as undirected)
# We'll build a graph where each city maps to a set of directly connected cities.
flight_edges = [
    ("Oslo", "Stockholm"),
    ("Krakow", "Frankfurt"),
    ("Krakow", "Istanbul"),
    ("Munich", "Stockholm"),
    ("Hamburg", "Stockholm"),
    ("Krakow", "Vilnius"),  # from Krakow to Vilnius assumed bidirectional
    ("Oslo", "Istanbul"),
    ("Istanbul", "Stockholm"),
    ("Oslo", "Krakow"),
    ("Vilnius", "Istanbul"),
    ("Oslo", "Vilnius"),
    ("Frankfurt", "Istanbul"),
    ("Oslo", "Frankfurt"),
    ("Munich", "Hamburg"),
    ("Munich", "Istanbul"),
    ("Oslo", "Munich"),
    ("Frankfurt", "Florence"),
    ("Oslo", "Hamburg"),
    ("Vilnius", "Frankfurt"),
    ("Florence", "Munich"),  # from Florence to Munich assumed bidirectional
    ("Krakow", "Munich"),
    ("Hamburg", "Istanbul"),
    ("Frankfurt", "Stockholm"),
    ("Stockholm", "Santorini"),  # from Stockholm to Santorini
    ("Frankfurt", "Munich"),
    ("Santorini", "Oslo"),       # from Santorini to Oslo
    ("Krakow", "Stockholm"),
    ("Vilnius", "Munich"),       # from Vilnius to Munich
    ("Frankfurt", "Hamburg")
]

# Build the flight graph dictionary
flight_graph = {city: set() for city in cities}
for a, b in flight_edges:
    flight_graph[a].add(b)
    flight_graph[b].add(a)

# Backtracking search to find a valid itinerary order (list of city names)
# Conditions to satisfy:
# 1. Consecutive cities must have a direct flight (connection exists in flight_graph).
# 2. Total unique days (overlapping flight days) equals TOTAL_UNIQUE_DAYS.
# 3. Istanbul must be visited on days 25-29 => its segment must start at day 25.
# 4. Krakow must include a workshop day between day 5 and day 9 (i.e. its segment 
#    must overlap the interval [5,9]). For a segment starting at S and lasting d days, 
#    it covers days S through S+d-1.
#
# The itinerary day calculation:
# - First city: covers day 1 to day d.
# - Each subsequent city: if previous city ended on day X then the next city starts on day X 
#   (overlap) and covers X to X + d - 1.
#
# Let T[i] be the finishing day of segment i.
# Then T[0] = duration(city0) and for i>=1, T[i] = T[i-1] + duration(city_i) - 1.
#
# We require that when Istanbul is added at some position i (i>=1),
# the start day for that segment (which is T[i-1]) equals 25.
# And for Krakow, if its segment covers days [S, E], then we require S <= 9 and E >= 5.

solution = None  # global variable to store a valid itinerary order

def backtrack(path, current_day):
    global solution
    # If a complete itinerary order is built, check if overall unique days match
    if len(path) == len(cities):
        if current_day == TOTAL_UNIQUE_DAYS:
            solution = list(path)
        return

    # Remaining cities to visit
    remaining = [city for city in cities if city not in path]
    
    for city in remaining:
        # If this is not the first city, check flight connection
        if path:
            last = path[-1]
            if city not in flight_graph[last]:
                continue

        # Determine the start day for this city segment
        # For the first city, start_day is 1; for others, it's the current_day (overlap)
        start_day = 1 if not path else current_day
        duration = cities[city]
        end_day = start_day + duration - 1
        new_total = end_day  # new current_day after adding this city

        # Prune if overshooting total days
        # Even if we overlap days in future, unique days only increase by (duration - 1)
        if new_total > TOTAL_UNIQUE_DAYS:
            continue

        # Special constraint for Istanbul: its segment must start exactly at day 25.
        if city == "Istanbul" and start_day != 25:
            continue

        # Special constraint for Krakow: its segment [start_day, end_day] must intersect [5, 9].
        if city == "Krakow":
            # There must be at least one day d such that 5 <= d <= 9 and start_day <= d <= end_day.
            if not (start_day <= 9 and end_day >= 5):
                continue

        # Estimate a lower bound for total unique days if we add the minimum possible from the remaining cities.
        # For each additional city, unique extra days are at least (duration - 1), and the smallest possible (duration-1)
        # among unvisited cities:
        extra = 0
        for r in remaining:
            if r == city:
                continue
            extra += (cities[r] - 1)
        possible_total = new_total + extra
        if possible_total < TOTAL_UNIQUE_DAYS:
            # Even with minimum additions, cannot reach total unique days
            continue

        # Add city and continue backtracking
        backtrack(path + [city], new_total)
        # If a solution is found, we can stop.
        if solution is not None:
            return

# Start backtracking. We do not allow Istanbul as the first city because it must start at day 25.
for start_city in cities:
    if start_city == "Istanbul":
        continue
    duration = cities[start_city]
    start_day = 1
    end_day = start_day + duration - 1
    # If starting city is Krakow, check workshop window [5,9]
    if start_city == "Krakow":
        if not (start_day <= 9 and end_day >= 5):
            continue
    # Also, if the first city causes too many unique days early, we skip.
    if end_day > TOTAL_UNIQUE_DAYS:
        continue
    backtrack([start_city], end_day)
    if solution is not None:
        break

# If no solution was found, set solution to empty.
if solution is None:
    solution = []

# Now, using the found ordering (solution), compute the day-ranges.
itinerary = []
if solution:
    # Compute finishing day (T) for each segment.
    # For the first city, days covered: 1 to duration.
    days = []
    current = 1
    for city in solution:
        duration = cities[city]
        end = current + duration - 1
        days.append((current, end))
        # Next city starts on the same day as the current segment's end (overlap)
        current = end
    # Build itinerary list using computed day ranges.
    for (start, end), city in zip(days, solution):
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

# Output the result as JSON-formatted dictionary.
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))