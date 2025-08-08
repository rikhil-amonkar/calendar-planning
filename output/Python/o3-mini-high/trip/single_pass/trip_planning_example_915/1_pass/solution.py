#!/usr/bin/env python3
import json
import itertools

# Define trip parameters
total_days = 26
cities = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
durations = {
    "Bucharest": 3,
    "Venice": 5,
    "Prague": 4,
    "Frankfurt": 5,
    "Zurich": 5,
    "Florence": 5,
    "Tallinn": 5
}

# Event constraints:
# Frankfurt: show from day 12 to day 16 => must be in Frankfurt from exactly day 12 to day 16.
# Tallinn: meet friends between day 8 and day 12 => its visit must overlap the window [8,12].
# Venice: wedding between day 22 and day 26 => its visit must overlap the window [22,26].

def check_event(city, start, end):
    if city == "Frankfurt":
        # Frankfurt must cover the show: [12, 16] exactly.
        if start != 12 or end != 16:
            return False
    elif city == "Tallinn":
        # Tallinn visit must intersect with window [8,12].
        if end < 8 or start > 12:
            return False
    elif city == "Venice":
        # Venice must intersect with window [22,26].
        if end < 22 or start > 26:
            return False
    return True

# Define the direct flight connections (assumed bidirectional unless noted otherwise).
# Each tuple (A, B) means there's a direct flight between A and B.
flight_edges = [
    ("Prague", "Tallinn"),
    ("Prague", "Zurich"),
    ("Florence", "Prague"),
    ("Frankfurt", "Bucharest"),
    ("Frankfurt", "Venice"),
    ("Prague", "Bucharest"),
    ("Bucharest", "Zurich"),
    ("Tallinn", "Frankfurt"),
    ("Frankfurt", "Zurich"),
    ("Zurich", "Venice"),
    ("Florence", "Frankfurt"),
    ("Prague", "Frankfurt"),
    ("Tallinn", "Zurich"),
    # Also one directional flight is given ("from Zurich to Florence"),
    # but for constructing a consistent itinerary we only add it in one direction.
    ("Zurich", "Florence")
]

# Build an undirected (bidirectional) flight graph.
graph = {city: set() for city in cities}
for a, b in flight_edges:
    # For the one directed edge from Zurich to Florence, add only if not already present in reverse.
    # But if the reverse edge appears then it is bidirectional.
    if (b, a) in flight_edges:
        graph[a].add(b)
        graph[b].add(a)
    else:
        # For the special "from Zurich to Florence" case, add only in the given direction.
        if a == "Zurich" and b == "Florence":
            graph[a].add(b)
        else:
            graph[a].add(b)
            graph[b].add(a)

# Check flight connectivity function for a given itinerary order.
def is_valid_connection(order):
    for i in range(len(order)-1):
        current = order[i]
        next_city = order[i+1]
        if next_city not in graph[current]:
            return False
    return True

# Compute the day ranges for a given itinerary order.
# According to the rule, if you fly from city A to city B on day X then day X is counted in both cities.
# We define:
#   For the first city, start_day = 1, end_day = start_day + duration - 1.
#   For each subsequent city, start_day = previous city's end_day, end_day = start_day + duration - 1.
def compute_schedule(order):
    schedule = []
    current_day = 1
    for city in order:
        start = current_day
        end = start + durations[city] - 1
        schedule.append((city, start, end))
        # Next city starts on the same day this city ended (flight day overlap)
        current_day = end
    return schedule

# Search over all permutations to find one valid itinerary that satisfies all constraints.
def find_itinerary():
    for perm in itertools.permutations(cities):
        # Check if consecutive city flights are available.
        if not is_valid_connection(perm):
            continue
        schedule = compute_schedule(perm)
        # Check overall trip days
        if schedule[-1][2] != total_days:
            continue
        valid = True
        for city, start, end in schedule:
            if not check_event(city, start, end):
                valid = False
                break
        if valid:
            return schedule
    return None

solution = find_itinerary()

if solution is None:
    result = {"itinerary": []}
else:
    # Format schedule as list of dicts with day_range and place.
    itinerary_list = []
    for city, start, end in solution:
        day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    result = {"itinerary": itinerary_list}

# Output the result as JSON
print(json.dumps(result))