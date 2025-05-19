#!/usr/bin/env python3
import json

# Input parameters and constraints
total_days = 19

# Durations required in each city (if visited without flight overlap)
durations = {
    "Reykjavik": 5,
    "Istanbul": 4,
    "Edinburgh": 5,
    "Oslo": 2,
    "Stuttgart": 3,
    "Bucharest": 5
}

# Direct flight availability (bidirectional assumed except where noted)
# Represented as a set of frozensets for symmetric connections.
flights = {
    frozenset(["Bucharest", "Oslo"]),
    frozenset(["Istanbul", "Oslo"]),
    frozenset(["Reykjavik", "Stuttgart"]),  # given as "from Reykjavik to Stuttgart", assumed symmetric
    frozenset(["Bucharest", "Istanbul"]),
    frozenset(["Stuttgart", "Edinburgh"]),
    frozenset(["Istanbul", "Edinburgh"]),
    frozenset(["Oslo", "Reykjavik"]),
    frozenset(["Istanbul", "Stuttgart"]),
    frozenset(["Oslo", "Edinburgh"])
}

# The itinerary must use exactly 5 flights (6 cities, with flight-day overlapping)
# so that the sum of durations minus the number of flights equals total_days:
#   sum(durations) - 5 = 19   -> sum(durations)=24.
#
# After exploring several combinations that meet the constraints:
# - Must spend 5 days in Reykjavik, 4 in Istanbul, 5 in Edinburgh, 2 in Oslo,
#   3 in Stuttgart, and 5 in Bucharest.
#
# - Additionally, one must be in Istanbul on at least one day between day 5 and day 8
#   (friend meeting) and in Oslo on at least one day between day 8 and day 9 (visit relatives).
#
# One valid ordering that satisfies the direct flight requirements and constraints is:
#   1. Bucharest (5 days)
#   2. Istanbul (4 days)
#   3. Oslo (2 days)
#   4. Edinburgh (5 days)
#   5. Stuttgart (3 days)
#   6. Reykjavik (5 days)
#
# Check flight connections:
#   Bucharest -> Istanbul: direct (Bucharest and Istanbul)
#   Istanbul -> Oslo: direct (Istanbul and Oslo)
#   Oslo -> Edinburgh: direct (Oslo and Edinburgh)
#   Edinburgh -> Stuttgart: direct (Stuttgart and Edinburgh)
#   Stuttgart -> Reykjavik: direct (Reykjavik and Stuttgart)
#
# Timeline calculation with flight-day overlaps:
#   City1: Bucharest: days 1-5.
#     (Fly on day 5, so Bucharest is day 1..5)
#   City2: Istanbul: days 5-8.
#     (Fly on day 8)
#   City3: Oslo: days 8-9.
#     (Fly on day 9)
#   City4: Edinburgh: days 9-13.
#     (Fly on day 13)
#   City5: Stuttgart: days 13-15.
#     (Fly on day 15)
#   City6: Reykjavik: days 15-19.
#
# Constraint verification:
#   - Istanbul: visited on days 5-8, so a day between 5 and 8 is included.
#   - Oslo: visited on days 8-9, so a day between 8 and 9 is included.
#   - Total days = 24 - 5 = 19.
#
# This is our computed itinerary.

# Define the itinerary (city order and duration from input parameters)
itinerary_plan = [
    {"place": "Bucharest", "duration": durations["Bucharest"]},
    {"place": "Istanbul", "duration": durations["Istanbul"]},
    {"place": "Oslo", "duration": durations["Oslo"]},
    {"place": "Edinburgh", "duration": durations["Edinburgh"]},
    {"place": "Stuttgart", "duration": durations["Stuttgart"]},
    {"place": "Reykjavik", "duration": durations["Reykjavik"]}
]

# Check that consecutive cities are connected by a direct flight.
def is_direct_flight(city_a, city_b):
    return frozenset([city_a, city_b]) in flights

for i in range(len(itinerary_plan) - 1):
    city_from = itinerary_plan[i]["place"]
    city_to = itinerary_plan[i+1]["place"]
    if not is_direct_flight(city_from, city_to):
        raise ValueError(f"No direct flight between {city_from} and {city_to}")

# Compute the day ranges.
# When flying from city A to city B on day X, that day counts for both cities.
# Thus, the start day of the first city is 1.
# For each subsequent city, its start day is the end day of the previous city.
schedule = []
current_day = 1
for segment in itinerary_plan:
    duration = segment["duration"]
    # The segment covers days from current_day to (current_day + duration - 1)
    start_day = current_day
    end_day = current_day + duration - 1
    schedule.append({
        "day_range": f"{start_day}-{end_day}",
        "place": segment["place"]
    })
    # For the next segment, the flight occurs on the last day of this segment,
    # so the next segment starts on the same day as the flight day.
    current_day = end_day

# Verify that the final day equals total_days.
if current_day != total_days:
    raise ValueError(f"Computed itinerary ends on day {current_day} but total days is {total_days}")

# Output the itinerary as JSON
output = {"itinerary": schedule}
print(json.dumps(output, indent=2))