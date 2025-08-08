#!/usr/bin/env python3
import json

# Trip parameters
total_days = 16
city_durations = {
    "Mykonos": 3,
    "Reykjavik": 2,
    "Dublin": 5,
    "London": 5,
    "Helsinki": 4,
    "Hamburg": 2
}

# Flight connectivity (bidirectional)
flight_graph = {
    "Dublin": ["London", "Hamburg", "Helsinki", "Reykjavik"],
    "London": ["Dublin", "Hamburg", "Reykjavik", "Mykonos", "Helsinki"],
    "Hamburg": ["Dublin", "London", "Helsinki"],
    "Helsinki": ["Reykjavik", "Dublin", "London", "Hamburg"],
    "Reykjavik": ["Helsinki", "London", "Dublin"],
    "Mykonos": ["London"]
}

# Constraint checking function.
# pos: position index in the itinerary (0-indexed)
# start, end: computed start and end day for the current city segment.
def meets_constraints(city, start, end, pos):
    # Hamburg: meet friends between day 1 and day 2.
    # Force Hamburg to be the very first city.
    if city == "Hamburg":
        if pos != 0:
            return False
        # With duration 2 and start day 1, Hamburg's interval will be 1-2.
        if not (start == 1 and end >= 2):
            return False
    # Dublin: annual show from day 2 to day 6.
    # Enforce Dublin to be the second city so that its interval covers day2-day6.
    if city == "Dublin":
        if pos != 1:
            return False
        # For Dublin (duration 5), the ideal is start==2 and end==6.
        if not (start <= 2 and end >= 6):
            return False
    # Reykjavik: wedding between day 9 and day 10.
    # For Reykjavik (duration 2), the only valid interval is exactly 9-10.
    if city == "Reykjavik":
        if start != 9 or end != 10:
            return False
    return True

# Backtracking search variables
solution = None

# Backtracking method:
# itinerary: list of segments already scheduled (each segment is a dict with keys "place" and "day_range")
# used: set of cities that have been scheduled
# current_day: the day when the next city segment will start.
def backtrack(itinerary, used, current_day):
    global solution
    # If a complete itinerary is constructed, check that last day's number equals total_days.
    if len(itinerary) == len(city_durations):
        if current_day == total_days:
            solution = itinerary.copy()
        return

    for city in city_durations:
        if city in used:
            continue

        # Enforce that Hamburg must be first.
        if len(itinerary) == 0 and city != "Hamburg":
            continue

        # Enforce that Dublin must be the second city (to attend the annual show from day 2 to 6).
        if len(itinerary) == 1 and city != "Dublin":
            continue

        # Check flight connectivity from the previous city if any.
        if itinerary:
            prev_city = itinerary[-1]["place"]
            if city not in flight_graph.get(prev_city, []):
                continue

        duration = city_durations[city]
        # If you fly on the same day, the current_day counts for both arrival and departure.
        end_day = current_day + duration - 1
        next_start = end_day  # Next city's start day equals the end day of the current city.

        if next_start > total_days:
            continue

        if not meets_constraints(city, current_day, end_day, len(itinerary)):
            continue

        itinerary.append({"place": city, "day_range": f"Day {current_day}-{end_day}"})
        used.add(city)
        backtrack(itinerary, used, next_start)
        if solution is not None:
            return
        itinerary.pop()
        used.remove(city)

# Start backtracking from day 1, with an empty itinerary.
backtrack([], set(), 1)

if solution is None:
    output = {"itinerary": []}
else:
    output = {"itinerary": solution}

print(json.dumps(output))