#!/usr/bin/env python3
import json
from copy import deepcopy

# Define the direct flight connections (treated as undirected)
flight_pairs = [
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

# Build the flight graph as an adjacency dictionary
def build_flight_graph(pairs):
    graph = {}
    for a, b in pairs:
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set()).add(a)
    return graph

flight_graph = build_flight_graph(flight_pairs)

# Define the required durations for each city
durations = {
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

# Total days calculation: sum(durations) - (number of transitions)
TOTAL_DAYS = sum(durations.values()) - (len(durations) - 1)  # Should be 23

# Event constraints:
# Wedding in Frankfurt must be between Day 1 and Day 5.
# For simplicity, we fix Frankfurt as the first city.
# Friends meeting in Mykonos: Mykonos must include Day 10 (and Day 11)
# For a 2-day stay, the only possibility to include both is to start on Day 10.
# Conference in Seville: For a 5-day stay, to include both Day 13 and Day 17,
# the Seville segment must start exactly on Day 13 (and end on Day 17).

# A helper function to check the special event constraints for a city given its segment.
def check_event(city, start_day, end_day):
    if city == "Mykonos":
        # Require that the 2-day stay covers day 10 and day 11.
        # With duration 2, the only possibility to cover day10 and day11 is start_day == 10 (segment: 10-11)
        if start_day != 10:
            return False
    if city == "Seville":
        # For a 5-day stay, require segment to be exactly day 13-17.
        if start_day != 13 or end_day != 17:
            return False
    # Frankfurt is fixed to be first so it will naturally be day 1 to 5.
    return True

# Given an ordering, the segments are determined by:
# - The first city's start_day is 1 and end_day = start_day + duration - 1.
# - For each subsequent city, its start_day equals the previous city's end_day (flight day overlap)
#   and its end_day = start_day + duration - 1.
def compute_schedule(order):
    schedule = []
    current_day = 1
    for city in order:
        start_day = current_day
        end_day = start_day + durations[city] - 1
        schedule.append((city, start_day, end_day))
        # Next city begins on the same day as this city's end_day (overlap counts as flight day)
        current_day = end_day
    return schedule

# Backtracking search for a valid itinerary order and schedule.
def search_itinerary(path, schedule, remaining):
    # If no cities remain, check final total days
    if not remaining:
        # The final city schedule's end should equal TOTAL_DAYS (=23)
        if schedule[-1][2] == TOTAL_DAYS:
            return path, schedule
        return None

    last_city = path[-1]
    # Get the current segment end_day of the last city:
    current_end = schedule[-1][2]
    # Try each possible next city that is directly connected to last_city.
    for city in list(remaining):
        if city not in flight_graph.get(last_city, set()):
            continue
        # Compute the next city segment start and end days.
        next_start = current_end  # flight day overlap: same day as last city's end
        next_end = next_start + durations[city] - 1
        # Check event constraints for this city if it is special.
        if not check_event(city, next_start, next_end):
            continue
        # Tentatively add this city
        new_path = path + [city]
        new_schedule = schedule + [(city, next_start, next_end)]
        new_remaining = remaining - {city}
        result = search_itinerary(new_path, new_schedule, new_remaining)
        if result is not None:
            return result
    return None

def main():
    # We fix Frankfurt as the first city because of the wedding constraint.
    initial_city = "Frankfurt"
    # Frankfurt must be day 1 to 1+5-1 = Day 5 (which satisfies the wedding constraint).
    initial_schedule = [(initial_city, 1, 1 + durations[initial_city] - 1)]
    remaining_cities = set(durations.keys()) - {initial_city}
    result = search_itinerary([initial_city], initial_schedule, remaining_cities)
    if result is None:
        itinerary_json = {"itinerary": []}
    else:
        order, sched = result
        # Format schedule into the desired output format.
        itinerary_list = []
        for city, start, end in sched:
            day_range = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range, "place": city})
        itinerary_json = {"itinerary": itinerary_list}
    print(json.dumps(itinerary_json, indent=2))

if __name__ == '__main__':
    main()