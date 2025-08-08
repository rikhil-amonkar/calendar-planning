#!/usr/bin/env python3
import json

# Trip constraints
total_trip_days = 18

# Cities with required durations (non-overlapped total sum = 25 days)
# Note: With 7 transitions (each flight day overlaps) the effective trip length is 25 - 7 = 18 days.
# Also incorporating specific scheduling constraints:
# - Oslo: 2 days and must be at the start (meeting friends between day1-2)
# - Dubrovnik: 3 days and must cover days 2-4 (annual show)
# - Helsinki: 2 days
# - Krakow: 5 days
# - Vilnius: 2 days
# - Paris: 2 days
# - Madrid: 5 days
# - Mykonos: 4 days and must be visited with relatives between day15-18
cities = [
    {"city": "Oslo", "duration": 2},
    {"city": "Dubrovnik", "duration": 3},
    {"city": "Helsinki", "duration": 2},
    {"city": "Krakow", "duration": 5},
    {"city": "Vilnius", "duration": 2},
    {"city": "Paris", "duration": 2},
    {"city": "Madrid", "duration": 5},
    {"city": "Mykonos", "duration": 4}
]

# Direct flights available.
# For bidirectional flights the connection is added both ways.
# Note: "from Krakow to Vilnius" is only available in that direction.
flight_connections = {
    "Oslo": {"Krakow", "Paris", "Madrid", "Helsinki", "Dubrovnik", "Vilnius"},
    "Krakow": {"Oslo", "Paris", "Vilnius"},  # Vilnius only in this (directed) case.
    "Paris": {"Oslo", "Madrid", "Krakow", "Helsinki", "Vilnius"},
    "Madrid": {"Paris", "Oslo", "Dubrovnik", "Helsinki", "Mykonos"},
    "Helsinki": {"Vilnius", "Oslo", "Krakow", "Dubrovnik", "Paris", "Madrid"},
    "Vilnius": {"Helsinki", "Oslo", "Paris"},
    "Dubrovnik": {"Helsinki", "Madrid", "Oslo"},
    "Mykonos": {"Madrid"}
}

# The chosen itinerary order must respect direct flights.
# Our planned order: Oslo -> Dubrovnik -> Helsinki -> Krakow -> Vilnius -> Paris -> Madrid -> Mykonos
itinerary_order = [city_info["city"] for city_info in cities]

# Check connectivity between consecutive cities in the itinerary_order.
# If a connection is not available, we exit by raising an Exception.
def validate_connections(order, flight_map):
    for i in range(len(order) - 1):
        origin = order[i]
        destination = order[i+1]
        # Check if destination is reachable from origin.
        if destination not in flight_map.get(origin, set()):
            raise Exception(f"No direct flight from {origin} to {destination}.")

try:
    validate_connections(itinerary_order, flight_connections)
except Exception as e:
    print(json.dumps({"error": str(e)}))
    exit(1)

# Compute day ranges for each city.
# Rule: We start on day 1 in the first city.
# When flying from city A to city B on day X, day X counts for both A and B.
itinerary_segments = []
current_day = 1

for city_info in cities:
    duration = city_info["duration"]
    city = city_info["city"]
    # The block covers current_day through (current_day + duration - 1)
    start_day = current_day
    end_day = current_day + duration - 1
    segment = {"day_range": f"Day {start_day}-{end_day}", "place": city}
    itinerary_segments.append(segment)
    # Overlap the last day for the next flight: next city starts on the same day as the current block's end.
    current_day = end_day

# The final day calculated should equal total_trip_days (=18)
if current_day != total_trip_days:
    print(json.dumps({"error": "Calculated itinerary does not meet the total trip days constraint."}))
    exit(1)

# Build the final itinerary dictionary with JSON structure.
trip_plan = {"itinerary": itinerary_segments}

# Output the result as JSON.
print(json.dumps(trip_plan))