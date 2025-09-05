#!/usr/bin/env python3
import json
import itertools
import sys

# City info: duration in days.
cities_info = {
    "Venice": 3,
    "Reykjavik": 2,
    "Munich": 3,
    "Santorini": 3,
    "Manchester": 3,
    "Porto": 3,
    "Bucharest": 5,
    "Tallinn": 4,
    "Valencia": 2,
    "Vienna": 5
}

# Special constraints on the start day:
# For a city with duration d, its visit is from start day s to end day (s+d-1)
# Constraint: If flying on day X then that day counts for both cities.
# Requirements:
# - Munich (3 days) must cover days 4-6. With d=3, the only possibility is s == 4 (so visit = [4,6]).
# - Santorini (3 days) must be visited with relatives between day 8 and day 10.
#   We'll require its visit to start exactly on day 8 (so visit = [8,10]).
# - Valencia (2 days) must have the workshop on day 14-15. With d=2, require s == 14 (so visit = [14,15]).
special_start_constraints = {
    "Munich": 4,
    "Santorini": 8,
    "Valencia": 14
}

# Direct flight connections (undirected). Each tuple represents a flight link.
flight_links = [
    ("Bucharest", "Manchester"),
    ("Munich", "Venice"),
    ("Santorini", "Manchester"),
    ("Vienna", "Reykjavik"),
    ("Venice", "Santorini"),
    ("Munich", "Porto"),
    ("Valencia", "Vienna"),
    ("Manchester", "Vienna"),
    ("Porto", "Vienna"),
    ("Venice", "Manchester"),
    ("Santorini", "Vienna"),
    ("Munich", "Manchester"),
    ("Munich", "Reykjavik"),
    ("Bucharest", "Valencia"),
    ("Venice", "Vienna"),
    ("Bucharest", "Vienna"),
    ("Porto", "Manchester"),
    ("Munich", "Valencia"),
    ("Valencia", "Porto"),
    ("Munich", "Bucharest"),
    ("Tallinn", "Munich"),
    ("Santorini", "Bucharest"),
    ("Munich", "Valencia")  # duplicate edge, ignore
]

# Build a set of frozensets for fast connectivity checking.
flights_set = set()
for a, b in flight_links:
    flights_set.add(frozenset([a, b]))

# Function to compute the itinerary timeline given an ordered list of cities.
def compute_timeline(order):
    timeline = []
    current_day = 1
    for city in order:
        duration = cities_info[city]
        start = current_day
        end = start + duration - 1
        timeline.append((start, end))
        # Next city's start is the same as this city's end (flight day overlap)
        current_day = end
    return timeline

# Check if the timeline satisfies the overall trip length (should be 24 days).
def valid_total_length(timeline):
    if timeline and timeline[-1][1] == 24:
        return True
    return False

# Check special start day constraint for cities that have one.
def check_special_constraints(order, timeline):
    for idx, city in enumerate(order):
        if city in special_start_constraints:
            required_start = special_start_constraints[city]
            start, end = timeline[idx]
            if start != required_start:
                return False
    return True

# Check flight connectivity for consecutive cities.
def check_flights(order):
    for i in range(1, len(order)):
        pair = frozenset([order[i-1], order[i]])
        if pair not in flights_set:
            return False
    return True

# Backtracking search for a valid itinerary.
# We use fixed positions based on reasoning:
#   - To have Munich with start==4 in a 3-day visit, the first city must have duration 4.
#     Only Tallinn has duration 4 so we force it to be first.
#   - Then Munich must come second.
#   - To have Santorini start on day 8, we force Santorini to be at index 3.
# Also, to allow Santorini to start on day 8, the city at index 2 must be a 3-day city whose visit ends at day 8.
#
# Fixed positions:
# index0: "Tallinn"
# index1: "Munich"
# index3: "Santorini"
#
# For index2, choose from 3-day cities that are not Santorini ("Venice", "Manchester", "Porto").
# The remaining 6 positions (index 4 through index 9) will be filled with the remaining cities.
def find_itinerary():
    fixed_order = [None] * 10
    fixed_order[0] = "Tallinn"
    fixed_order[1] = "Munich"
    fixed_order[3] = "Santorini"
    
    # For index2, choose one candidate from 3-day cities (exclude "Santorini")
    candidates_index2 = [city for city in ["Venice", "Manchester", "Porto"] if cities_info[city] == 3]
    
    all_cities = set(cities_info.keys())
    # Pre-fix the ones that are forced:
    forced = {"Tallinn", "Munich", "Santorini"}
    
    for city2 in candidates_index2:
        fixed_order[2] = city2
        used = set(fixed_order[:4])
        remaining = list(all_cities - used)
        # There are 6 positions left: indices 4,5,6,7,8,9
        for perm in itertools.permutations(remaining, 6):
            candidate_order = fixed_order[:4] + list(perm)
            timeline = compute_timeline(candidate_order)
            # Check overall trip length: final end day must be 24.
            if not valid_total_length(timeline):
                continue
            # Check special start constraints for Munich, Santorini, Valencia if present.
            if not check_special_constraints(candidate_order, timeline):
                continue
            # Check flight connectivity for every consecutive pair.
            if not check_flights(candidate_order):
                continue
            # If we reached here, we found a valid itinerary.
            return candidate_order, timeline
    return None, None

def main():
    order, timeline = find_itinerary()
    if order is None:
        result = {"itinerary": []}
    else:
        itinerary = []
        for city, (start, end) in zip(order, timeline):
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()