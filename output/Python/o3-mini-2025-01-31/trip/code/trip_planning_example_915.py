#!/usr/bin/env python3
import json

# Trip constraints and durations for each city
# Total trip length = 26 days, but note that if a flight occurs on day X,
# that day counts as being in both the departure and arrival cities.
# Thus, if we have 7 cities with durations d1,...,d7 then overall days = sum(d_i) - (7-1) = 32 - 6 = 26.
#
# The input fixed durations are:
# Bucharest: 3 days
# Venice: 5 days (and must include a wedding between day 22 and day 26)
# Prague: 4 days
# Frankfurt: 5 days (and must include an annual show from day 12 to day 16)
# Zurich: 5 days
# Florence: 5 days
# Tallinn: 5 days (and must include friend meeting between day 8 and day 12)
#
# Our task is to order these cities so that:
# 1. The cumulative day ranges match the constraints.
# 2. The direct flight connections between consecutive cities (segments) exist.
#
# The flights available (bidirectional unless marked otherwise):
# - Prague <-> Tallinn
# - Prague <-> Zurich
# - Florence <-> Prague
# - Frankfurt <-> Bucharest
# - Frankfurt <-> Venice
# - Prague <-> Bucharest
# - Bucharest <-> Zurich
# - Tallinn <-> Frankfurt
# - Zurich -> Florence        (we use as bidirectional: Florence <-> Zurich not explicitly provided but we will prefer other flights)
# - Frankfurt <-> Zurich
# - Zurich <-> Venice
# - Florence <-> Frankfurt
# - Prague <-> Frankfurt
# - Tallinn <-> Zurich
#
# After examining several orders, one valid itinerary that meets all constraints is:
#
# Order of cities (segments) and their assigned durations:
# Segment 1: Florence (5 days)
# Segment 2: Prague   (4 days)
# Segment 3: Tallinn  (5 days)  --> Covers friend meeting between day 8 and 12.
# Segment 4: Frankfurt(5 days)   --> Must cover day 12 to 16 for the annual show.
# Segment 5: Bucharest (3 days)
# Segment 6: Zurich    (5 days)
# Segment 7: Venice    (5 days)   --> Wedding event between day 22 and 26.
#
# Let us check flight connectivity between consecutive cities:
# Florence -> Prague: (Florence and Prague exists)
# Prague   -> Tallinn: (Prague and Tallinn exists)
# Tallinn  -> Frankfurt: (Tallinn and Frankfurt exists)
# Frankfurt-> Bucharest: (Frankfurt and Bucharest exists)
# Bucharest-> Zurich: (Bucharest and Zurich exists)
# Zurich   -> Venice: (Zurich and Venice exists)
#
# Now determine the day ranges:
# The rule: For the first city the range is 1 to d1.
# For subsequent city i, the range is: [previous_end_day, previous_end_day + (d_i - 1)]
#
# Let cumulative_day = 1 initially.
# For city 1 (Florence, 5 days): days 1 to 5.
# City 2 (Prague, 4 days): starts on day 5 (flight day from Florence, counts for both),
#    so days 5 to 5 + 4 - 1 = 5 to 8.
# City 3 (Tallinn, 5 days): starts on day 8, so days 8 to 8 + 5 - 1 = 8 to 12.
# City 4 (Frankfurt, 5 days): starts on day 12, so days 12 to 12 + 5 - 1 = 12 to 16.
# City 5 (Bucharest, 3 days): starts on day 16, so days 16 to 16 + 3 - 1 = 16 to 18.
# City 6 (Zurich, 5 days): starts on day 18, so days 18 to 18 + 5 - 1 = 18 to 22.
# City 7 (Venice, 5 days): starts on day 22, so days 22 to 22 + 5 - 1 = 22 to 26.
#
# This itinerary satisfies:
# - Tallinn (segment 3) covers days 8 to 12 (meeting with friends).
# - Frankfurt (segment 4) covers days 12 to 16 (annual show).
# - Venice (segment 7) covers days 22 to 26 (wedding event).
# - All direct flights exist between consecutive cities.
#
# Now we compute and output the itinerary as JSON containing just "day_range" and "place" for each segment.

cities = [
    {"name": "Florence", "duration": 5},
    {"name": "Prague", "duration": 4},
    {"name": "Tallinn", "duration": 5},
    {"name": "Frankfurt", "duration": 5},
    {"name": "Bucharest", "duration": 3},
    {"name": "Zurich", "duration": 5},
    {"name": "Venice", "duration": 5},
]

itinerary = []
current_day = 1

for city in cities:
    dur = city["duration"]
    # For the first city, the itinerary covers days current_day to current_day + dur - 1.
    # For subsequent cities, the departure day is the first day of the segment (which is
    # the same as the arrival day, because flight day is double counted).
    start_day = current_day
    end_day = current_day + dur - 1
    itinerary.append({
        "day_range": f"{start_day}-{end_day}",
        "place": city["name"]
    })
    # For next city, the new current_day is the end_day (flight day is overlap)
    current_day = end_day

# Output the itinerary as a JSON-formatted dictionary.
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))