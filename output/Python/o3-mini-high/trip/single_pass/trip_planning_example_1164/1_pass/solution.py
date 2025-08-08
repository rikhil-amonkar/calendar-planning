#!/usr/bin/env python3
import json

# Trip constraints and data
total_itinerary_days = 17

cities = {
    "Nice": {"duration": 3},
    "Reykjavik": {"duration": 2, "event": {"window": (3, 4)}},     # meet friend between day 3 and 4
    "Stockholm": {"duration": 2, "event": {"window": (4, 5)}},      # meet friend between day 4 and 5
    "Split": {"duration": 3},
    "Copenhagen": {"duration": 2},
    "Venice": {"duration": 4},
    "Vienna": {"duration": 3, "event": {"window": (11, 13)}},       # workshop between day 11 and 13
    "Porto": {"duration": 5, "event": {"window": (13, 17)}}         # wedding between day 13 and 17
}

# List of direct flight connections (bidirectional)
edges = [
    ("Copenhagen", "Vienna"),
    ("Nice", "Stockholm"),
    ("Split", "Copenhagen"),
    ("Nice", "Reykjavik"),
    ("Nice", "Porto"),
    ("Reykjavik", "Vienna"),
    ("Stockholm", "Copenhagen"),
    ("Nice", "Venice"),
    ("Nice", "Vienna"),
    ("Reykjavik", "Copenhagen"),
    ("Nice", "Copenhagen"),
    ("Stockholm", "Vienna"),
    ("Venice", "Vienna"),
    ("Copenhagen", "Porto"),
    ("Reykjavik", "Stockholm"),
    ("Stockholm", "Split"),
    ("Split", "Vienna"),
    ("Copenhagen", "Venice"),
    ("Vienna", "Porto")
]

# Build an undirected graph from the edges
graph = {}
for city in cities:
    graph[city] = set()
for (a, b) in edges:
    if a in cities and b in cities:
        graph[a].add(b)
        graph[b].add(a)

# Global variable to store a valid itinerary if found.
found_solution = None

# Compute the schedule given an itinerary order.
# The rule: S1 starts Day 1 and covers [1, duration1].
# For each subsequent city, its start day is equal to the previous city's end day (flight day overlap),
# and it covers [start, start + duration - 1].
def compute_schedule(itinerary):
    schedule = []
    current_day = 1
    for city in itinerary:
        dur = cities[city]["duration"]
        start = current_day
        end = start + dur - 1
        schedule.append({"city": city, "start": start, "end": end})
        current_day = end  # next city's start day is this flight day (overlap)
    return schedule

# Check if each city that has an event meets its date window.
def satisfies_events(schedule):
    for seg in schedule:
        city = seg["city"]
        if "event" in cities[city]:
            window_start, window_end = cities[city]["event"]["window"]
            # The segment [start, end] must intersect with the event window.
            if seg["end"] < window_start or seg["start"] > window_end:
                return False
    return True

# Depth-first search to find a valid itinerary (permutation of cities)
def dfs(path, used):
    global found_solution
    if found_solution is not None:
        return
    if len(path) == len(cities):
        schedule = compute_schedule(path)
        # Total days must equal total_itinerary_days (this is automatic from given durations, but we check)
        if schedule[-1]["end"] != total_itinerary_days:
            return
        if satisfies_events(schedule):
            found_solution = (list(path), schedule)
        return
    for city in cities:
        if city in used:
            continue
        if not path:
            path.append(city)
            used.add(city)
            dfs(path, used)
            if found_solution is not None:
                return
            path.pop()
            used.remove(city)
        else:
            last_city = path[-1]
            if city in graph[last_city]:
                path.append(city)
                used.add(city)
                dfs(path, used)
                if found_solution is not None:
                    return
                path.pop()
                used.remove(city)

dfs([], set())

if found_solution is None:
    output = {"itinerary": []}
else:
    itinerary_order, schedule_data = found_solution
    # Build JSON-friendly output with day-range strings.
    itinerary_list = []
    for seg in schedule_data:
        day_range = "Day {}-{}".format(seg["start"], seg["end"])
        itinerary_list.append({"day_range": day_range, "place": seg["city"]})
    output = {"itinerary": itinerary_list}

print(json.dumps(output))