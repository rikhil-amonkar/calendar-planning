#!/usr/bin/env python3
import json
import itertools

# Total trip and city parameters
total_days = 26

# Cities and their required minimum stay durations (in days)
durations = {
    "Venice": 4,
    "Barcelona": 3,
    "Copenhagen": 4,
    "Reykjavik": 4,
    "Dubrovnik": 5,
    "Athens": 2,
    "Tallinn": 5,
    "Munich": 3,
    "Lyon": 4
}

# Event constraints: each event city has a required global day window (inclusive)
# Friend meeting in Barcelona between day 10 and 12,
# Relatives in Copenhagen between day 7 and 10,
# Wedding in Dubrovnik between day 16 and 20.
event_windows = {
    "Barcelona": (10, 12),
    "Copenhagen": (7, 10),
    "Dubrovnik": (16, 20)
}

# List of cities (order does not matter; we will search for a permutation)
cities = list(durations.keys())

# Direct flight connections given (treating them as bidirectional).
flight_pairs = [
    ("Copenhagen", "Athens"),
    ("Copenhagen", "Dubrovnik"),
    ("Munich", "Tallinn"),
    ("Copenhagen", "Munich"),
    ("Venice", "Munich"),
    ("Reykjavik", "Athens"),  # provided as "from Reykjavik to Athens"; assume bidirectional
    ("Athens", "Dubrovnik"),
    ("Venice", "Athens"),
    ("Lyon", "Barcelona"),
    ("Copenhagen", "Reykjavik"),
    ("Reykjavik", "Munich"),
    ("Athens", "Munich"),
    ("Lyon", "Munich"),
    ("Barcelona", "Reykjavik"),
    ("Venice", "Copenhagen"),
    ("Barcelona", "Dubrovnik"),
    ("Lyon", "Venice"),
    ("Dubrovnik", "Munich"),
    ("Barcelona", "Athens"),
    ("Copenhagen", "Barcelona"),
    ("Venice", "Barcelona"),
    ("Barcelona", "Munich"),
    ("Barcelona", "Tallinn"),
    ("Copenhagen", "Tallinn")
]

# Build a set of allowed flight connections as frozensets of city names.
# (This makes checking bidirectionality simple.)
allowed_flights = set()
for (a, b) in flight_pairs:
    allowed_flights.add(frozenset((a, b)))

# Function to check if a flight exists between two cities.
def flight_exists(city_a, city_b):
    return frozenset((city_a, city_b)) in allowed_flights

# Given a complete ordering of cities, compute the itinerary schedule.
# On the first city, we start at Day 1.
# For each subsequent city, the flight occurs on the last day of the previous stay,
# meaning that day counts as the first day for the next city.
def compute_schedule(order):
    schedule = []
    current_day = 1
    for city in order:
        start_day = current_day
        finish_day = start_day + durations[city] - 1
        schedule.append((city, start_day, finish_day))
        # Next city starts on the same day as the finish_day (flight day overlapping)
        current_day = finish_day
    return schedule

# Check if the schedule for a city satisfies its event window (if any).
def event_satisfied(city, start_day, finish_day):
    if city not in event_windows:
        return True
    window_start, window_end = event_windows[city]
    # There is an overlap if the city's stay from start_day to finish_day
    # shares at least one day with the window [window_start, window_end].
    if finish_day < window_start or start_day > window_end:
        return False
    return True

# Check if a complete itinerary ordering satisfies flight connectivity and event constraints.
def valid_itinerary(order):
    # Check flight connectivity for consecutive cities.
    for i in range(len(order) - 1):
        if not flight_exists(order[i], order[i+1]):
            return False
    # Compute the full schedule.
    schedule = compute_schedule(order)
    # The overall itinerary should span exactly total_days.
    if schedule[-1][2] != total_days:
        return False
    # Check event constraints for cities with events.
    for city, start_day, finish_day in schedule:
        if not event_satisfied(city, start_day, finish_day):
            return False
    return True

# Search for a valid permutation of cities
found_schedule = None
for perm in itertools.permutations(cities):
    if valid_itinerary(perm):
        found_schedule = compute_schedule(perm)
        break

# If a valid schedule is found, format the itinerary for JSON output.
if found_schedule:
    itinerary_output = []
    for (city, start_day, finish_day) in found_schedule:
        itinerary_output.append({
            "day_range": f"Day {start_day}-{finish_day}",
            "place": city
        })
    result = {"itinerary": itinerary_output}
else:
    result = {"itinerary": []}

print(json.dumps(result))