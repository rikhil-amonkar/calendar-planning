#!/usr/bin/env python3
import itertools
import json

# Input variables: total days and cities with their required durations.
total_days = 20
cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]

# Each city is to be visited for a fixed number of days.
durations = {
    "Oslo": 2,
    "Reykjavik": 5,
    "Stockholm": 4,
    "Munich": 4,
    "Frankfurt": 4,
    "Barcelona": 3,
    "Bucharest": 2,
    "Split": 3
}

# Absolute date constraints (if the city is visited, its calendar segment must satisfy these):
# For a segment visited as the i-th city, if its start day (computed by cumulative durations with overlaps)
# does not match the value below then the permutation is invalid.
abs_start_constraints = {
    "Munich": 13,      # Must be visited so that the segment begins on day 13 (covering days 13-16) 
    "Oslo": 16,        # Must cover the annual show on day 16-17.
    "Frankfurt": 17    # Must cover the workshop between day 17 and day 20.
}
# Additional constraint for Reykjavik: The friend meeting must occur sometime between day 9 and day 13.
# This is interpreted as the Reykjavik visit interval [start, end] having a nonempty intersection with [9,13].
def meets_friend_constraint(start, end):
    # There is an intersection with [9,13] if start <= 13 and end >= 9.
    return start <= 13 and end >= 9

# The traveler only takes direct flights.
# List of 24 allowed direct flight pairs. We treat them as bidirectional.
allowed_flights_list = [
    ("Reykjavik", "Munich"),
    ("Munich", "Frankfurt"),
    ("Split", "Oslo"),
    ("Reykjavik", "Oslo"),
    ("Bucharest", "Munich"),
    ("Oslo", "Frankfurt"),
    ("Bucharest", "Barcelona"),
    ("Barcelona", "Frankfurt"),
    ("Reykjavik", "Frankfurt"),
    ("Barcelona", "Stockholm"),
    ("Barcelona", "Reykjavik"),
    ("Stockholm", "Reykjavik"),
    ("Barcelona", "Split"),
    ("Bucharest", "Oslo"),
    ("Bucharest", "Frankfurt"),
    ("Split", "Stockholm"),
    ("Barcelona", "Oslo"),
    ("Stockholm", "Munich"),
    ("Stockholm", "Oslo"),
    ("Split", "Frankfurt"),
    ("Barcelona", "Munich"),
    ("Stockholm", "Frankfurt"),
    ("Munich", "Oslo"),
    ("Split", "Munich")
]
allowed_flights = set(frozenset(pair) for pair in allowed_flights_list)

# Given an ordering of cities, compute the calendar schedule.
# The rule is: the first city's visit starts on day 1.
# When flying from one city to the next on day X, that day belongs to both the departing and arriving city.
# Thus, if a city is visited for d days, its calendar range is from start_day to (start_day + d - 1),
# and the next city starts on the same day as the previous city's end day.
def compute_schedule(order):
    schedule = []
    current_day = 1
    for city in order:
        d = durations[city]
        start_day = current_day
        end_day = start_day + d - 1
        schedule.append((city, start_day, end_day))
        # Next city starts on the same day as this city's last day.
        current_day = end_day
    return schedule

# Check if a candidate schedule meets all the imposed constraints.
def valid_schedule(schedule, order):
    # Check that the final day equals total_days.
    if schedule[-1][2] != total_days:
        return False
    # Check absolute start constraints for Munich, Oslo, and Frankfurt.
    for city, start, end in schedule:
        if city in abs_start_constraints:
            if start != abs_start_constraints[city]:
                return False
        # Check Reykjavik friend meeting constraint.
        if city == "Reykjavik":
            if not meets_friend_constraint(start, end):
                return False
    # Check direct flight connectivity between consecutive cities.
    for (city1, _, _), (city2, _, _) in zip(schedule, schedule[1:]):
        if frozenset([city1, city2]) not in allowed_flights:
            return False
    return True

# The total sum of durations is 27 and with 7 flights (overlap days) the trip lasts 20 days.
# We now try every permutation of the 8 cities to find an itinerary that satisfies all constraints.
# To reduce search, we iterate over permutations of the sorted list.
solution_schedule = None
for perm in itertools.permutations(sorted(cities)):
    sched = compute_schedule(perm)
    if valid_schedule(sched, perm):
        solution_schedule = sched
        break

# If a valid itinerary is found, format it as requested.
if solution_schedule is None:
    result = {"itinerary": []}
else:
    itinerary_list = []
    for city, start, end in solution_schedule:
        day_range = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range, "place": city})
    result = {"itinerary": itinerary_list}

# Output the result as a JSON-formatted dictionary.
print(json.dumps(result))