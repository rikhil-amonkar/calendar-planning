#!/usr/bin/env python3
import json

# Define trip parameters and constraints
total_days = 28

# Required duration (in days) for each city (when counted with flight‐day overlaps)
durations = {
    "London": 3,      # Annual show from day 1 to 3.
    "Milan": 5,       # Must meet friends between day 3 and 7.
    "Zurich": 2,      # Conference on day 7 and day 8.
    "Bucharest": 2,
    "Hamburg": 5,
    "Barcelona": 4,
    "Reykjavik": 5,   # Relatives must be visited between day 9 and 13.
    "Stuttgart": 5,
    "Stockholm": 2,
    "Tallinn": 4
}

# For our planning, we have fixed absolute constraints:
# - London must be visited on day 1-3.
# - Milan must be visited early so that the friend meeting can be between day 3 and 7.
# - Zurich must cover conference day 7 and 8.
# - Reykjavik must cover day 9-13 for relatives.
#
# To satisfy both flight rules (if flying on day X then day X counts for both cities)
# and the total unique days (sum(durations) - (#transitions) = 28), we set up an itinerary order.
#
# We choose the following order:
#   S1: London
#   S2: Milan
#   S3: Zurich
#   S4: Stockholm   (Used as a spacer so that the following Reykjavik block starts on day 9)
#   S5: Reykjavik
#   S6: Stuttgart
#   S7: Hamburg
#   S8: Bucharest
#   S9: Barcelona
#   S10: Tallinn
#
# This order yields:
#   London: Day 1-3
#   Milan: Day 3-7        (overlap on day 3 with London, friend meeting happens between day 3 and 7)
#   Zurich: Day 7-8       (overlap on day 7 with Milan; conference on day 7 and 8)
#   Stockholm: Day 8-9    (overlap on day 8 with Zurich)
#   Reykjavik: Day 9-13   (overlap on day 9 with Stockholm; relatives visited on days 9-13)
#   Stuttgart: Day 13-17  (overlap on day 13 with Reykjavik)
#   Hamburg: Day 17-21    (overlap on day 17 with Stuttgart)
#   Bucharest: Day 21-22  (overlap on day 21 with Hamburg)
#   Barcelona: Day 22-25  (overlap on day 22 with Bucharest)
#   Tallinn: Day 25-28    (overlap on day 25 with Barcelona)
#
# This ordering also obeys the available direct flight connections.

# Define the itinerary order with required segments
itinerary_order = [
    "London",
    "Milan",
    "Zurich",
    "Stockholm",
    "Reykjavik",
    "Stuttgart",
    "Hamburg",
    "Bucharest",
    "Barcelona",
    "Tallinn"
]

# List of direct flight connections (treat as undirected edges)
# We use frozenset of two cities for each flight.
flight_list = [
    frozenset(["London", "Hamburg"]),
    frozenset(["London", "Reykjavik"]),
    frozenset(["Milan", "Barcelona"]),
    frozenset(["Reykjavik", "Barcelona"]),
    frozenset(["Reykjavik", "Stuttgart"]),  # given as "from Reykjavik to Stuttgart"
    frozenset(["Stockholm", "Reykjavik"]),
    frozenset(["London", "Stuttgart"]),
    frozenset(["Milan", "Zurich"]),
    frozenset(["London", "Barcelona"]),
    frozenset(["Stockholm", "Hamburg"]),
    frozenset(["Zurich", "Barcelona"]),
    frozenset(["Stockholm", "Stuttgart"]),
    frozenset(["Milan", "Hamburg"]),
    frozenset(["Stockholm", "Tallinn"]),
    frozenset(["Hamburg", "Bucharest"]),
    frozenset(["London", "Bucharest"]),
    frozenset(["Milan", "Stockholm"]),
    frozenset(["Stuttgart", "Hamburg"]),
    frozenset(["London", "Zurich"]),
    frozenset(["Milan", "Reykjavik"]),
    frozenset(["London", "Stockholm"]),
    frozenset(["Milan", "Stuttgart"]),
    frozenset(["Stockholm", "Barcelona"]),
    frozenset(["London", "Milan"]),
    frozenset(["Zurich", "Hamburg"]),
    frozenset(["Bucharest", "Barcelona"]),
    frozenset(["Zurich", "Stockholm"]),
    frozenset(["Barcelona", "Tallinn"]),
    frozenset(["Zurich", "Reykjavik"]),
    frozenset(["Zurich", "Bucharest"])
]

# Helper function to check if a direct flight exists between two cities.
def has_direct_flight(city1, city2):
    return frozenset([city1, city2]) in flight_list

# Verify that the chosen itinerary order is valid according to direct flight connections.
for i in range(len(itinerary_order) - 1):
    a = itinerary_order[i]
    b = itinerary_order[i+1]
    if not has_direct_flight(a, b):
        raise ValueError(f"No direct flight between {a} and {b} as required by the itinerary.")

# Calculate day ranges for each segment.
# The rule is: if flying from city A to city B on day X, then day X is counted in both cities.
# We assume that each transition uses the last day of the previous segment as the overlapping day.
itinerary_segments = []
current_start = 1
for city in itinerary_order:
    d = durations[city]
    # The segment covers 'd' days counting the start day. 
    # So if the segment starts at current_start, it ends at (current_start + d - 1)
    current_end = current_start + d - 1
    itinerary_segments.append({
        "day_range": f"Day {current_start}-{current_end}",
        "place": city
    })
    # For the next segment, the flight day is the overlapping day: next segment starts on current_end.
    current_start = current_end

# Build final itinerary dictionary
result = {"itinerary": itinerary_segments}

# Output the result as JSON
print(json.dumps(result))