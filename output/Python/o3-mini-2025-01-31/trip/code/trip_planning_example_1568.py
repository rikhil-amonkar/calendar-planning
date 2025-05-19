#!/usr/bin/env python3
import json

# We fix a specific order of cities that respects both the flight connectivity 
# (based on the provided direct flights) and the constraints.
cities = [
    {"name": "Vienna", "duration": 5, "constraint": lambda s, e: (s <= 5 and e >= 1)},         # must meet friend in Vienna between day1-5
    {"name": "Prague", "duration": 5, "constraint": lambda s, e: (s <= 9 and e >= 5)},         # annual show from day5 to day9
    {"name": "Munich", "duration": 2, "constraint": lambda s, e: True},
    {"name": "Split", "duration": 3, "constraint": lambda s, e: (s <= 13 and e >= 11)},        # relatives between day11 and day13
    {"name": "Amsterdam", "duration": 3, "constraint": lambda s, e: True},
    {"name": "Riga", "duration": 2, "constraint": lambda s, e: (s <= 16 and e >= 15)},         # meet friend in Riga between day15 and day16
    {"name": "Stockholm", "duration": 2, "constraint": lambda s, e: (s <= 17 and e >= 16)},      # conference in Stockholm during day16 and day17
    {"name": "Istanbul", "duration": 2, "constraint": lambda s, e: True},
    {"name": "Brussels", "duration": 2, "constraint": lambda s, e: True},
    {"name": "Seville", "duration": 3, "constraint": lambda s, e: True},
]

# We require that the overall trip spans exactly 20 unique days.
TOTAL_DAYS = 20

# For each consecutive pair in the itinerary, we require that there is an overlap day 
# (representing the flight day when the traveler is in both cities).
def intervals_overlap(s1, e1, s2, e2):
    return not (e1 < s2 or e2 < s1)

# Backtracking search to assign start days for each city. 
# The assigned interval for a city with start day s and duration d is [s, s+d-1].
# We fix the first city to start at day 1 and force the last city's end day = TOTAL_DAYS.
def backtrack(index, assignments):
    if index == len(cities):
        # Check overall itinerary span: earliest day should be 1 and latest end day equal to TOTAL_DAYS.
        ends = [assignments[i] + cities[i]["duration"] - 1 for i in range(len(cities))]
        if min(assignments) == 1 and max(ends) == TOTAL_DAYS:
            return assignments
        return None

    city = cities[index]
    d = city["duration"]
    # The latest possible start for this city so that its end does not exceed TOTAL_DAYS is:
    latest_start = TOTAL_DAYS - d + 1
    # If this is the first city, fix start = 1.
    if index == 0:
        candidate = 1
        end = candidate + d - 1
        # Must satisfy its personal constraint.
        if not city["constraint"](candidate, end):
            return None
        assignments.append(candidate)
        result = backtrack(index + 1, assignments)
        if result is not None:
            return result
        assignments.pop()
        return None

    # For the last city, we want its end exactly = TOTAL_DAYS.
    if index == len(cities) - 1:
        # Last city start must be TOTAL_DAYS - d + 1.
        candidate = TOTAL_DAYS - d + 1
        end = candidate + d - 1
        if not city["constraint"](candidate, end):
            return None
        # Also check overlapping constraint with previous city.
        prev_index = index - 1
        prev_start = assignments[prev_index]
        prev_end = prev_start + cities[prev_index]["duration"] - 1
        # There must be overlap between previous city and this one.
        if not intervals_overlap(prev_start, prev_end, candidate, end):
            return None
        assignments.append(candidate)
        result = backtrack(index + 1, assignments)
        if result is not None:
            return result
        assignments.pop()
        return None

    # For intermediate cities, try all possible start days from 1 to latest_start.
    for candidate in range(1, latest_start + 1):
        end = candidate + d - 1
        # Must satisfy the city's own constraint.
        if not city["constraint"](candidate, end):
            continue
        # And must not extend past TOTAL_DAYS (we allow cities to overlap by flights)
        if end > TOTAL_DAYS:
            continue
        # Also, ensure overlap with previously assigned city.
        prev_start = assignments[index - 1]
        prev_end = prev_start + cities[index - 1]["duration"] - 1
        if not intervals_overlap(prev_start, prev_end, candidate, end):
            continue
        # Additionally, we want the timeline to be monotonic (non-decreasing start days)
        # to roughly follow the order.
        if assignments and candidate < assignments[-1]:
            continue
        assignments.append(candidate)
        result = backtrack(index + 1, assignments)
        if result is not None:
            return result
        assignments.pop()
    return None

solution = backtrack(0, [])
if solution is None:
    itinerary = {"error": "No valid itinerary found"}
else:
    itinerary = []
    for i, city in enumerate(cities):
        start = solution[i]
        end = start + city["duration"] - 1
        # For output, we use a dictionary with day_range and place.
        itinerary.append({"day_range": f"{start}-{end}", "place": city["name"]})

# Output the itinerary as a JSON-formatted dictionary (list of day ranges and places)
print(json.dumps(itinerary, indent=2))