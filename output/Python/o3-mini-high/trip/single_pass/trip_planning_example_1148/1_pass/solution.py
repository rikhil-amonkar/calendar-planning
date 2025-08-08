#!/usr/bin/env python3
import json

# Trip constraints as input variables

# Total calendar days for the trip
TOTAL_DAYS = 19

# List of cities and required number of days spent (including flight overlap)
# The total sum over cities (minus overlap for each flight day) equals TOTAL_DAYS.
city_durations = {
    "Lisbon": 2,
    "Dubrovnik": 5,
    "Copenhagen": 5,
    "Prague": 3,
    "Tallinn": 2,
    "Stockholm": 4,
    "Split": 3,
    "Lyon": 2
}

# Event constraints: for each city with an event, the city’s allocated day range must cover the event interval.
# Format: city: (event_start, event_end)
event_constraints = {
    "Tallinn": (1, 2),      # Meet friend in Tallinn between day 1 and day 2
    "Lisbon": (4, 5),       # Workshop in Lisbon between day 4 and day 5
    "Stockholm": (13, 16),  # Wedding in Stockholm between day 13 and day 16
    "Lyon": (18, 19)        # Annual show in Lyon from day 18 to day 19
}

# Direct flights between cities (bidirectional)
flight_edges = [
    ("Dubrovnik", "Stockholm"),
    ("Lisbon", "Copenhagen"),
    ("Lisbon", "Lyon"),
    ("Copenhagen", "Stockholm"),
    ("Copenhagen", "Split"),
    ("Prague", "Stockholm"),
    ("Tallinn", "Stockholm"),
    ("Prague", "Lyon"),
    ("Lisbon", "Stockholm"),
    ("Prague", "Lisbon"),
    ("Stockholm", "Split"),
    ("Prague", "Copenhagen"),
    ("Split", "Lyon"),
    ("Copenhagen", "Dubrovnik"),
    ("Prague", "Split"),
    ("Tallinn", "Copenhagen"),
    ("Tallinn", "Prague"),
]

# Build a flight connectivity dictionary (bidirectional)
flights = {}
for city in city_durations:
    flights[city] = set()
for (a, b) in flight_edges:
    if a in flights and b in flights:
        flights[a].add(b)
        flights[b].add(a)

cities = list(city_durations.keys())

# Backtracking search for a valid itinerary order.
# We determine the day schedule along with the order.
# Note: if we fly from A to B on day X, then X is counted in both cities.
# We set the schedule such that:
#   S[0] = 1, E[0] = 1 + duration(A) - 1.
#   For i > 0: S[i] = E[i-1], and E[i] = S[i] + duration(city) - 1.
#
# The overall calendar days will always equal: duration(city1) + sum_{i=2}^{n}(duration(city_i)-1)
# which by design will be TOTAL_DAYS if all constraints hold.

def backtrack(order, current_start):
    # If all cities are placed, return the order.
    if len(order) == len(cities):
        return order

    for city in cities:
        if city in order:
            continue

        # If there is a previous city, check direct flight connectivity.
        if order:
            prev_city = order[-1]
            if city not in flights[prev_city]:
                continue

        # Compute end day for this city: end = current_start + duration - 1
        duration = city_durations[city]
        end_day = current_start + duration - 1

        # Check event constraint if any on this city.
        if city in event_constraints:
            evt_start, evt_end = event_constraints[city]
            # The allocated days in the city must cover the event interval.
            if current_start > evt_start or end_day < evt_end:
                continue

        # For partial orders, we can also prune if the event window for a city that must be early
        # is already impossible later.
        # For example, if "Tallinn" (friend meeting) is not placed first,
        # then its allocated start day would be > 1. So if city is Tallinn and current_start > 1, skip.
        if city == "Tallinn" and current_start > 1:
            continue
        # Similarly, if "Lisbon" must cover day 4-5, and current_start is already too late.
        if city == "Lisbon" and current_start > event_constraints["Lisbon"][0]:
            continue
        # For Stockholm and Lyon the event windows are later, so no extra prune here.

        # Recursively backtrack with city added.
        new_order = order + [city]
        # Next city will start at the flight day which is the same as the current city's end_day.
        result = backtrack(new_order, end_day)
        if result is not None:
            return result

    return None

# Compute the itinerary day ranges given an order.
def compute_schedule(order):
    schedule = []
    current_day = 1
    for city in order:
        duration = city_durations[city]
        start_day = current_day
        end_day = start_day + duration - 1
        schedule.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        # Next city's start day is the same as the current city's end day (flight day overlap).
        current_day = end_day
    return schedule

def main():
    order = backtrack([], 1)
    if order is None:
        output = {"itinerary": []}
    else:
        itinerary = compute_schedule(order)
        output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()