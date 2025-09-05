#!/usr/bin/env python3
import itertools
import json

# Define the cities and their required durations (in days)
durations = {
    "Naples": 3,
    "Valencia": 5,
    "Stuttgart": 2,
    "Split": 5,
    "Venice": 5,
    "Amsterdam": 4,
    "Nice": 2,
    "Barcelona": 2,
    "Porto": 4
}

cities = list(durations.keys())

# Define the direct flight connections (bidirectional)
flight_edges = [
    ("Venice", "Nice"),
    ("Naples", "Amsterdam"),
    ("Barcelona", "Nice"),
    ("Amsterdam", "Nice"),
    ("Stuttgart", "Valencia"),
    ("Stuttgart", "Porto"),
    ("Split", "Stuttgart"),
    ("Split", "Naples"),
    ("Valencia", "Amsterdam"),
    ("Barcelona", "Porto"),
    ("Valencia", "Naples"),
    ("Venice", "Amsterdam"),
    ("Barcelona", "Naples"),
    ("Barcelona", "Valencia"),
    ("Split", "Amsterdam"),
    ("Barcelona", "Venice"),
    ("Stuttgart", "Amsterdam"),
    ("Naples", "Nice"),
    ("Venice", "Stuttgart"),
    ("Split", "Barcelona"),
    ("Porto", "Nice"),
    ("Barcelona", "Stuttgart"),
    ("Venice", "Naples"),
    ("Porto", "Amsterdam"),
    ("Porto", "Valencia"),
    ("Stuttgart", "Naples"),
    ("Barcelona", "Amsterdam")
]

# Build a flight graph as a dictionary: each city maps to a set of cities with direct flights.
flight_graph = {city: set() for city in cities}
for a, b in flight_edges:
    flight_graph[a].add(b)
    flight_graph[b].add(a)

# Special event constraints.
# For Venice: must be present on day 6 and day 10.
# For Barcelona: must be present on at least one day in {5,6} (workshop).
# For Naples: must be present on at least one day in {18,19,20} (meeting a friend).
# For Nice: must be present on at least one day in {23,24} (tour with friends).
event_requirements = {
    "Venice": {"must_have": {6, 10}},   # Both day 6 and 10 must be included.
    "Barcelona": {"must_have": {5, 6}},
    "Naples": {"must_have": {18, 19, 20}},
    "Nice": {"must_have": {23, 24}}
}

# Given the rule: if you fly on a day, you count as being in both cities.
# We construct the itinerary timeline as follows:
# For the first city, start on day 1 and end on day (1 + duration - 1).
# For each subsequent city, start = previous end, and end = start + duration - 1.
def compute_itinerary(route):
    itinerary = []
    current_day = 1
    for city in route:
        d = durations[city]
        start = current_day
        end = start + d - 1
        itinerary.append({"city": city, "start": start, "end": end})
        # Next city starts on the same day as the previous flight day (overlap)
        current_day = end
    return itinerary

# Check if the flight connectivity is valid for the route.
def flights_ok(route):
    for i in range(len(route) - 1):
        if route[i+1] not in flight_graph[route[i]]:
            return False
    return True

# Check if the scheduled timeline meets the special event day requirements.
def events_ok(itinerary):
    for segment in itinerary:
        city = segment["city"]
        start = segment["start"]
        end = segment["end"]
        days_in_city = set(range(start, end + 1))
        if city in event_requirements:
            # For Venice, require that both day 6 and day 10 are in its range.
            required = event_requirements[city]["must_have"]
            if not required.issubset(days_in_city):
                return False
    return True

# Due to the Barcelona and Naples and Nice events we need their days to fall in a very narrow window.
# We can add additional checks for these cities (since durations are short).
def additional_event_checks(itinerary):
    for segment in itinerary:
        city = segment["city"]
        start = segment["start"]
        end = segment["end"]
        days_in_city = set(range(start, end + 1))
        if city == "Barcelona":
            # Workshop must occur between day 5 and 6: at least one day must be 5 or 6.
            if days_in_city.isdisjoint({5, 6}):
                return False
        if city == "Naples":
            # Friend meeting between day 18 and 20.
            if days_in_city.isdisjoint({18, 19, 20}):
                return False
        if city == "Nice":
            # Tour with friends between day 23 and 24.
            if days_in_city.isdisjoint({23, 24}):
                return False
    return True

# Main search: iterate over permutations of the 9 cities.
# The total unique days of the itinerary must be 24.
# (Total city-days sum is 32; the overlap in 8 flights yields 32 - 8 = 24 unique days.)
solution = None
for route in itertools.permutations(cities):
    # First, check that consecutive cities have a flight.
    if not flights_ok(route):
        continue

    # Compute the itinerary timeline based on the route.
    itinerary = compute_itinerary(route)
    # Check that the final end day equals 24.
    if itinerary[-1]["end"] != 24:
        continue

    # Check special event constraints.
    if not events_ok(itinerary):
        continue
    if not additional_event_checks(itinerary):
        continue

    # If all constraints are satisfied, we have a valid itinerary.
    solution = itinerary
    break

# Format the result as specified.
result = {"itinerary": []}
if solution:
    for segment in solution:
        day_range = f"Day {segment['start']}-{segment['end']}"
        result["itinerary"].append({"day_range": day_range, "place": segment["city"]})
else:
    result = {"itinerary": "No valid itinerary found."}

# Output the result as JSON.
print(json.dumps(result, indent=2))