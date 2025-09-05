import json
import itertools

# Input variables (trip constraints)
total_trip_days = 22

# Required durations for each city
durations = {
    "Istanbul": 5,    # Must include annual show from Day 1-5.
    "Brussels": 3,
    "Helsinki": 3,
    "Split": 4,
    "Dubrovnik": 2,
    "Milan": 4,
    "Frankfurt": 3,   # Wedding must occur here between Day 16 and Day 18.
    "Vilnius": 5      # Workshop in Vilnius must occur between Day 18 and Day 22.
}

# Flight connections.
# Each tuple represents (city_A, city_B, directed)
# For undirected connections, directed is False (and the reverse connection is allowed).
# For directed flights, the flight is allowed only in the order given.
flights = [
    ("Milan", "Frankfurt", False),
    ("Split", "Frankfurt", False),
    ("Milan", "Split", False),
    ("Brussels", "Vilnius", False),
    ("Brussels", "Helsinki", False),
    ("Istanbul", "Brussels", False),
    ("Milan", "Vilnius", False),
    ("Brussels", "Milan", False),
    ("Istanbul", "Helsinki", False),
    ("Helsinki", "Vilnius", False),
    ("Helsinki", "Dubrovnik", False),
    ("Split", "Vilnius", False),
    ("Dubrovnik", "Istanbul", True),    # Directed: only from Dubrovnik to Istanbul.
    ("Istanbul", "Milan", False),
    ("Helsinki", "Frankfurt", False),
    ("Istanbul", "Vilnius", False),
    ("Split", "Helsinki", False),
    ("Milan", "Helsinki", False),
    ("Istanbul", "Frankfurt", False),
    ("Brussels", "Frankfurt", True),      # Directed: only from Brussels to Frankfurt.
    ("Dubrovnik", "Frankfurt", False),
    ("Frankfurt", "Vilnius", False)
]

# Build the flight graph as a dictionary mapping each city to a set of connected cities.
graph = {}
for a, b, directed in flights:
    if a not in graph:
        graph[a] = set()
    graph[a].add(b)
    if not directed:
        if b not in graph:
            graph[b] = set()
        graph[b].add(a)
# Ensure all cities have an entry in the graph.
for city in durations:
    if city not in graph:
        graph[city] = set()

# Time window constraints (as (window_start, window_end)) for events:
time_windows = {
    "Istanbul": (1, 5),      # Istanbul must cover Day 1 to Day 5 (annual show).
    "Frankfurt": (16, 18),   # Wedding in Frankfurt must occur between Day 16 and Day 18.
    "Vilnius": (18, 22)      # Workshop in Vilnius must occur between Day 18 and Day 22.
}

# Function to compute each city’s day range given an itinerary order.
# The rule: first city uses its full duration; for each subsequent city,
# the flight day (which is the previous city's end day) counts as the first day.
def compute_day_ranges(order, durations):
    day_ranges = {}
    current_start = 1
    for idx, city in enumerate(order):
        d = durations[city]
        # For every city, the itinerary "day range" is defined as:
        # start = current_start, end = current_start + d - 1.
        start = current_start
        end = current_start + d - 1
        day_ranges[city] = (start, end)
        # For all but the last city, the flight to the next city happens on the end day.
        current_start = end
    return day_ranges

# Function to check if a given city's day range overlaps the required window.
def valid_time_window(day_range, window):
    start, end = day_range
    win_start, win_end = window
    return end >= win_start and start <= win_end

# Function to check if there is a valid direct flight from city_a to city_b.
def can_fly(city_a, city_b, graph):
    return city_b in graph.get(city_a, set())

# Search for a valid itinerary ordering.
# We fix Istanbul as the start (to cover its early show)
# and Vilnius as the final destination (to fully cover the workshop timing).
all_cities = list(durations.keys())
fixed_first = "Istanbul"
fixed_last = "Vilnius"
remaining_cities = [city for city in all_cities if city not in {fixed_first, fixed_last}]

valid_order = None
valid_day_ranges = None

for perm in itertools.permutations(remaining_cities):
    order = [fixed_first] + list(perm) + [fixed_last]
    
    # Check that every consecutive pair is connected by a flight.
    valid_flights = True
    for i in range(len(order) - 1):
        if not can_fly(order[i], order[i+1], graph):
            valid_flights = False
            break
    if not valid_flights:
        continue

    # Compute the day ranges for this itinerary order.
    day_ranges = compute_day_ranges(order, durations)
    
    # The overall trip duration is defined as the end day of the final city.
    overall_duration = day_ranges[order[-1]][1]
    if overall_duration != total_trip_days:
        continue

    # Check the time window constraint for Istanbul.
    if not valid_time_window(day_ranges["Istanbul"], time_windows["Istanbul"]):
        continue

    # Check the time window constraint for Frankfurt.
    if "Frankfurt" in order:
        if not valid_time_window(day_ranges["Frankfurt"], time_windows["Frankfurt"]):
            continue

    # Check the time window constraint for Vilnius.
    if "Vilnius" in order:
        if not valid_time_window(day_ranges["Vilnius"], time_windows["Vilnius"]):
            continue

    # If all constraints are satisfied, we have found a valid itinerary.
    valid_order = order
    valid_day_ranges = day_ranges
    break

# Build the output itinerary list with day ranges.
output = {}
itinerary_list = []

if valid_order is not None:
    for city in valid_order:
        start, end = valid_day_ranges[city]
        itinerary_list.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    output["itinerary"] = itinerary_list
else:
    output["itinerary"] = []

# Output the result as JSON.
print(json.dumps(output))