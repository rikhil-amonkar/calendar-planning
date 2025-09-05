import itertools
import json

# Define cities, durations, and event windows (inclusive)
cities = ["Nice", "Reykjavik", "Stockholm", "Split", "Copenhagen", "Venice", "Vienna", "Porto"]

durations = {
    "Nice": 3,
    "Reykjavik": 2,
    "Stockholm": 2,
    "Split": 3,
    "Copenhagen": 2,
    "Venice": 4,
    "Vienna": 3,
    "Porto": 5
}

# Event windows for cities that have specific appointments.
# For each, the itinerary segment for that city must overlap with the given window.
# e.g., Reykjavik must have at least one day in [3,4]
event_windows = {
    "Reykjavik": (3, 4),
    "Stockholm": (4, 5),
    "Vienna": (11, 13),
    "Porto": (13, 17)
}

# Allowed direct flight connections (undirected)
allowed_flights = [
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

# Build an undirected graph of allowed flights.
graph = {city: set() for city in cities}
for a, b in allowed_flights:
    graph[a].add(b)
    graph[b].add(a)

def compute_timeline(order):
    """
    Given an ordering (list) of cities, compute a timeline.
    By rule, the first city starts on Day 1.
    If city A has duration d and city B is visited next (by flight on the same day),
    then A is visited through days [start, start+d-1] and B is visited starting on day = (start+d-1).
    """
    timeline = []
    start_day = 1
    for city in order:
        d = durations[city]
        end_day = start_day + d - 1
        timeline.append((start_day, end_day))
        # Flight day: you leave A on its last day and arrive at B the same day.
        start_day = end_day
    return timeline

def event_ok(city, start, end):
    """
    Check if the interval [start, end] for the given city
    overlaps with its event window (if one exists).
    """
    if city in event_windows:
        window_start, window_end = event_windows[city]
        # Overlap condition: city interval [start, end] must satisfy:
        # start <= window_end and end >= window_start.
        return start <= window_end and end >= window_start
    return True

def is_valid_order(order, timeline):
    # Check flight connectivity between consecutive cities.
    for i in range(len(order) - 1):
        if order[i+1] not in graph[order[i]]:
            return False
    # Check event constraints for those cities with appointments.
    for city, (start, end) in zip(order, timeline):
        if not event_ok(city, start, end):
            return False
    return True

# Search for a valid ordering that satisfies all constraints
valid_itinerary = None
for perm in itertools.permutations(cities):
    timeline = compute_timeline(perm)
    # Since total days = sum(durations)=24 and 7 flight transitions overlap,
    # the trip lasts 24 - 7 = 17 days. (This always holds regardless of order.)
    if is_valid_order(perm, timeline):
        valid_itinerary = (perm, timeline)
        break

if valid_itinerary is None:
    result = {"itinerary": []}
else:
    order, timeline = valid_itinerary
    itinerary = []
    for city, (start, end) in zip(order, timeline):
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
    result = {"itinerary": itinerary}

# Output the itinerary as a JSON-formatted dictionary.
print(json.dumps(result))