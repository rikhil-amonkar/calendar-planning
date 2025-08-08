#!/usr/bin/env python3
import itertools
import json

# Input trip constraints

# Total trip days (unique days, after accounting for flight overlaps)
total_unique_days = 17

# Cities to visit and required durations (in days)
durations = {
    "Brussels": 5,
    "Rome": 2,
    "Dubrovnik": 3,
    "Geneva": 5,
    "Budapest": 2,
    "Riga": 4,
    "Valencia": 2
}

# Special time constraints:
# For a city visited in segment i, computed day range is [start, end] (inclusive)
# Constraint for Brussels: the stay must include at least one day in [7, 11]
def satisfies_brussels(start, end):
    return not (end < 7 or start > 11)

# Constraint for Budapest: the stay must include at least one day in [16, 17]
def satisfies_budapest(start, end):
    return not (end < 16 or start > 17)

# Constraint for Riga: the stay must include at least one day in [4, 7]
def satisfies_riga(start, end):
    return not (end < 4 or start > 7)

# Flight connections (only direct flights allowed)
# We represent the flight network as a dictionary mapping each city to the list of cities
# that can be reached by a direct flight.
# Most flights are bi-directional, except for "from Rome to Riga" which is only one‐way.
flight_graph = {
    "Brussels": ["Valencia", "Geneva", "Budapest", "Rome"],  # Brussels-Valencia, Brussels-Geneva, Brussels-Budapest, Brussels-Rome
    "Rome": ["Valencia", "Geneva", "Budapest", "Brussels", "Dubrovnik", "Riga"],  # Note: Rome->Riga is one-way and Dubrovnik connection as well
    "Dubrovnik": ["Geneva", "Rome"],  # Dubrovnik-Geneva, Dubrovnik-Rome
    "Geneva": ["Brussels", "Rome", "Dubrovnik", "Valencia", "Budapest"],
    "Budapest": ["Geneva", "Rome", "Brussels"],  # from Budapest, only these are allowed as per list
    "Riga": ["Brussels"],  # Riga <-> Brussels is allowed
    "Valencia": ["Brussels", "Rome", "Geneva"]
}

# List of all cities to visit
cities = list(durations.keys())

# Function to compute day ranges for a given itinerary order.
# According to the rule, if you fly from city A to city B on day X,
# then day X is counted for both A and B.
# We define the start day for the first city as day 1.
# For i > 0, start_day[i] = start_day[i-1] + durations[city_{i-1}] - 1.
def compute_day_ranges(order):
    day_ranges = []
    start_day = 1
    for city in order:
        end_day = start_day + durations[city] - 1
        day_ranges.append((start_day, end_day))
        # Next city starts on the same day as the previous city's end day.
        start_day = end_day
    return day_ranges

# Check if a given itinerary order satisfies flight connectivity and time constraints.
def valid_itinerary(order, day_ranges):
    # Check that the itinerary has the correct total duration.
    # Unique days passed = sum(durations) - (number of transitions)
    if day_ranges[-1][1] != total_unique_days:
        return False
    
    # Check flight connections for each consecutive pair.
    for i in range(len(order) - 1):
        if order[i+1] not in flight_graph.get(order[i], []):
            return False

    # Check time constraints for special cities.
    for city, (start, end) in zip(order, day_ranges):
        if city == "Brussels" and not satisfies_brussels(start, end):
            return False
        if city == "Budapest" and not satisfies_budapest(start, end):
            return False
        if city == "Riga" and not satisfies_riga(start, end):
            return False
    return True

# Use backtracking / permutation search to find a valid order that satisfies all constraints.
def find_itinerary():
    # We iterate over all permutations of the cities.
    # (There are 7! = 5040 possibilities, which is acceptable for this problem.)
    for perm in itertools.permutations(cities):
        # Compute day ranges for this ordering.
        day_ranges = compute_day_ranges(perm)
        if valid_itinerary(perm, day_ranges):
            return perm, day_ranges
    return None, None

def main():
    itinerary_order, day_ranges = find_itinerary()
    if itinerary_order is None:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        for (city, (start, end)) in zip(itinerary_order, day_ranges):
            itinerary_list.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
        result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()