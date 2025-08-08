#!/usr/bin/env python3
import json

# Define the required durations for each city
cities = {
    "Rome": 3,
    "Mykonos": 2,
    "Lisbon": 2,
    "Frankfurt": 5,
    "Nice": 3,
    "Stuttgart": 4,
    "Venice": 4,
    "Dublin": 2,
    "Bucharest": 2,
    "Seville": 5
}

# List of direct flights (bidirectional)
flight_list = [
    ("Rome", "Stuttgart"),
    ("Venice", "Rome"),
    ("Dublin", "Bucharest"),
    ("Mykonos", "Rome"),
    ("Seville", "Lisbon"),
    ("Frankfurt", "Venice"),
    ("Venice", "Stuttgart"),
    ("Bucharest", "Lisbon"),
    ("Nice", "Mykonos"),
    ("Venice", "Lisbon"),
    ("Dublin", "Lisbon"),
    ("Venice", "Nice"),
    ("Rome", "Seville"),
    ("Frankfurt", "Rome"),
    ("Nice", "Dublin"),
    ("Rome", "Bucharest"),
    ("Frankfurt", "Dublin"),
    ("Rome", "Dublin"),
    ("Venice", "Dublin"),
    ("Rome", "Lisbon"),
    ("Frankfurt", "Lisbon"),
    ("Nice", "Rome"),
    ("Frankfurt", "Nice"),
    ("Frankfurt", "Stuttgart"),
    ("Frankfurt", "Bucharest"),
    ("Lisbon", "Stuttgart"),
    ("Nice", "Lisbon"),
    ("Seville", "Dublin")
]

# Build a set of bidirectional connections using frozenset.
flight_set = set()
for a, b in flight_list:
    flight_set.add(frozenset([a, b]))

def is_connected(city1, city2):
    return frozenset([city1, city2]) in flight_set

# Backtracking search for a valid itinerary.
# Each itinerary entry is a tuple: (city, start_day, end_day)
# The rule is: the first city starts on day 1.
# If a city has duration d and is entered on day X,
# its interval is [X, X + d - 1] and the next city is entered on day (X + d - 1).
def backtrack(itin, current_time):
    # If we have visited all 10 cities, ensure the last city's end day is exactly 23.
    if len(itin) == len(cities):
        if itin[-1][2] == 23:
            return itin
        return None

    used = set([city for city, s, e in itin])
    last_city = itin[-1][0]
    for city in cities:
        if city in used:
            continue
        # Enforce flight connectivity: the next city must be directly connected with the last visited city.
        if not is_connected(last_city, city):
            continue

        # The start day for this city is the current_time.
        start_day = current_time
        duration = cities[city]
        end_day = start_day + duration - 1

        # Special constraints:
        # 1. Wedding in Frankfurt must be attended between day 1 and day 5.
        #    To ensure this, force Frankfurt to be the very first city.
        if city == "Frankfurt" and itin:
            continue  # Frankfurt already must be first.

        # 2. Meet friends in Mykonos on day 10 & 11.
        #    With a 2-day visit, Mykonos must start exactly on day 10.
        if city == "Mykonos" and start_day != 10:
            continue

        # 3. Attend the conference in Seville on day 13 and day 17.
        #    With a 5-day visit, Seville must start exactly on day 13.
        if city == "Seville" and start_day != 13:
            continue

        new_itin = itin + [(city, start_day, end_day)]
        new_current = end_day  # Next city is entered on the same day as the last day of this city.
        result = backtrack(new_itin, new_current)
        if result is not None:
            return result
    return None

def main():
    # Start with Frankfurt as the first city.
    start_day = 1
    duration = cities["Frankfurt"]
    end_day = start_day + duration - 1  # 1 + 5 - 1 = 5
    # Frankfurt's interval [1,5] satisfies the wedding constraint.
    itinerary = [("Frankfurt", start_day, end_day)]
    current_time = end_day  # Next city is entered on day 5.

    solution = backtrack(itinerary, current_time)
    result = {}
    if solution is None:
        result["itinerary"] = []
    else:
        # Format the solution into a list of day_range and place.
        formatted = []
        for city, s, e in solution:
            formatted.append({"day_range": f"Day {s}-{e}", "place": city})
        result["itinerary"] = formatted

    print(json.dumps(result))

if __name__ == "__main__":
    main()