#!/usr/bin/env python3
import json
import itertools

# Input trip constraints and parameters
total_days = 19

# Cities with required durations (days)
city_durations = {
    "Dubrovnik": 5,
    "Warsaw": 2,
    "Stuttgart": 7,
    "Bucharest": 6,
    "Copenhagen": 3
}

# Direct flight connections (bidirectional)
# Represent each connection as a frozenset of the two cities.
flight_connections = {
    frozenset(["Warsaw", "Copenhagen"]),
    frozenset(["Stuttgart", "Copenhagen"]),
    frozenset(["Warsaw", "Stuttgart"]),
    frozenset(["Bucharest", "Copenhagen"]),
    frozenset(["Bucharest", "Warsaw"]),
    frozenset(["Copenhagen", "Dubrovnik"])
}

# Fixed constraints: 
# - Wedding in Bucharest must happen on at least one day between day 1 and day 6.
# - Conference: Must be in Stuttgart on day 7 and day 13.
wedding_city = "Bucharest"
wedding_day_range = range(1, 7)  # Days 1 to 6 (inclusive)
conference_city = "Stuttgart"
conference_days = [7, 13]

# A helper function to simulate the itinerary timeline.
# We assume the itinerary is made of segments in order.
# For the first segment, days = [start, start+1, ..., end]
# For subsequent segments, the flight day is the start day and appears in both segments.
# We compute each segment's start and end day.
def compute_segments(order, durations):
    segments = []  # Each segment: (city, start, end)
    current_day = 1
    for city in order:
        start_day = current_day
        # The city is allocated its full duration; the day on which one flies is counted in both segments.
        end_day = start_day + durations[city] - 1
        segments.append((city, start_day, end_day))
        # The next segment starts on the same day as this one ends (flight day overlap)
        current_day = end_day
    return segments

# Build a day-to-cities mapping from segments.
def build_day_mapping(segments, total_days):
    day_to_cities = {day: set() for day in range(1, total_days+1)}
    # For each segment, add the city to each day in its interval.
    # Note: if a day is the overlapping flight day (start day in segments except the first),
    # it will get added twice from two adjacent segments.
    for city, start, end in segments:
        for day in range(start, end + 1):
            if 1 <= day <= total_days:
                day_to_cities[day].add(city)
    return day_to_cities

# Check if a given itinerary (order of cities) satisfies flight connectivity.
def valid_flight_connections(order, flight_connections):
    for i in range(len(order) - 1):
        if frozenset([order[i], order[i+1]]) not in flight_connections:
            return False
    return True

# Check if the itinerary day mapping satisfies the conference and wedding constraints.
def valid_event_constraints(day_to_cities):
    # Wedding: some day between day 1 and day 6 must include Bucharest.
    wedding_ok = any(wedding_city in day_to_cities[day] for day in wedding_day_range)
    # Conference: day 7 and day 13 must include Stuttgart.
    conf_ok = all(conference_city in day_to_cities.get(day, set()) for day in conference_days)
    return wedding_ok and conf_ok

# The total days computed from segments should equal total_days.
def valid_total_days(segments, total_days):
    # The final segment end day should equal total_days.
    if segments:
        return segments[-1][2] == total_days
    return False

def main():
    cities = list(city_durations.keys())
    valid_itinerary = None

    # Try all permutations of the cities:
    for order in itertools.permutations(cities):
        # Check flight connectivity along the itinerary
        if not valid_flight_connections(order, flight_connections):
            continue

        # Compute segments using the rule:
        # S0: days 1 to d0, S1: starts at day d0, ends at d0 + d1 - 1, etc.
        segments = compute_segments(order, city_durations)
        
        # Check if overall unique days match the total_days.
        if not valid_total_days(segments, total_days):
            continue

        # Build day mapping for the itinerary
        day_map = build_day_mapping(segments, total_days)
        
        # Check event constraints: 
        # Wedding in Bucharest between day 1-6 and Conference in Stuttgart on day 7 and day 13.
        if not valid_event_constraints(day_map):
            continue

        # If all constraints satisfied, we choose this itinerary.
        valid_itinerary = segments
        break

    # Build JSON output structure.
    output = {"itinerary": []}
    if valid_itinerary:
        for city, start, end in valid_itinerary:
            output["itinerary"].append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
    else:
        output["itinerary"] = []

    print(json.dumps(output))

if __name__ == '__main__':
    main()