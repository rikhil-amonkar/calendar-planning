#!/usr/bin/env python3
import json

# Input parameters and constraints
# Total itinerary is 32 days. There are 10 cities with required durations.
# Note: When flying on a day, the day is counted in both the departure and arrival cities.
# Durations (in days) as required:
# - Krakow: 5 days; NOTE: must include a workshop day between day 5 and day 9.
# - Frankfurt: 4 days
# - Florence: 2 days
# - Munich: 5 days
# - Hamburg: 5 days
# - Oslo: 5 days
# - Vilnius: 5 days
# - Istanbul: 5 days; NOTE: must include the annual show from day 25 to day 29.
# - Stockholm: 3 days
# - Santorini: 2 days
#
# We must also obey the direct flight connectivity:
#   Krakow -> Frankfurt (allowed: "Krakow and Frankfurt")
#   Frankfurt -> Florence (allowed: "Frankfurt and Florence")
#   Florence -> Munich (allowed: "from Florence to Munich")
#   Munich -> Hamburg (allowed: "Munich and Hamburg")
#   Hamburg -> Oslo (allowed: "Oslo and Hamburg")
#   Oslo -> Vilnius (allowed: "Oslo and Vilnius")
#   Vilnius -> Istanbul (allowed: "Vilnius and Istanbul")
#   Istanbul -> Stockholm (allowed: "Istanbul and Stockholm")
#   Stockholm -> Santorini (allowed: "from Stockholm to Santorini")
#
# Additionally, the workshop in Krakow should occur between day 5 and day 9.
# Since Krakow is scheduled first with a 5-day block (days 1-5), day 5 is available.
# The Istanbul block must cover days 25-29.
# We place Istanbul in the itinerary so that its 5-day span is exactly days 25 to 29.
#
# To create an itinerary with overlapping flight days:
#  We assume the itinerary is partitioned into 10 segments. When flying from city A to city B,
#  the flight day is the last day of city A’s segment and the first day of city B’s segment.
#  Therefore if the required duration (d) is met by each segment via:
#      segment_duration = end_day - start_day + 1 = d,
#  the overall timeline length is: sum(durations) - (number of flights).
#  With durations = [5,4,2,5,5,5,5,5,3,2] and 9 flight overlaps, the timeline length is:
#      5+4+2+5+5+5+5+5+3+2 - 9 = 41 - 9 = 32 days.
#
# We choose an ordering that meets both the flight network and timing constraints.
# We use the following order:
#   1. Krakow (5 days)         : days 1 - 5.
#   2. Frankfurt (4 days)       : overlapping day 5 -> days 5 - 8.
#   3. Florence (2 days)        : overlapping day 8 -> days 8 - 9.
#   4. Munich (5 days)          : overlapping day 9 -> days 9 - 13.
#   5. Hamburg (5 days)         : overlapping day 13 -> days 13 - 17.
#   6. Oslo (5 days)            : overlapping day 17 -> days 17 - 21.
#   7. Vilnius (5 days)         : overlapping day 21 -> days 21 - 25.
#   8. Istanbul (5 days)        : overlapping day 25 -> days 25 - 29.
#   9. Stockholm (3 days)       : overlapping day 29 -> days 29 - 31.
#  10. Santorini (2 days)       : overlapping day 31 -> days 31 - 32.
#
# Verification:
# - Krakow: days 1-5. (Workshop at day 5)
# - Istanbul: days 25-29. (Annual show days 25-29)
#
# Flight connections:
#   Krakow -> Frankfurt ("Krakow and Frankfurt")
#   Frankfurt -> Florence ("Frankfurt and Florence")
#   Florence -> Munich ("from Florence to Munich")
#   Munich -> Hamburg ("Munich and Hamburg")
#   Hamburg -> Oslo ("Oslo and Hamburg")
#   Oslo -> Vilnius ("Oslo and Vilnius")
#   Vilnius -> Istanbul ("Vilnius and Istanbul")
#   Istanbul -> Stockholm ("Istanbul and Stockholm")
#   Stockholm -> Santorini ("from Stockholm to Santorini")
#
# Calculation:
# For city i, if d[i] is its required days, and we have an overlap of 1 day with the previous city (if i > 0),
# then the start day for the first city is 1 and for any city i (i >= 1):
#   start_day[i] = 1 + (sum(d[0] ... d[i-1]) - i)
#   end_day[i] = start_day[i] + d[i] - 1
#
# The itinerary computed below automatically satisfies total days = 32.

# Define the cities in the chosen order with their required durations.
cities = [
    {"name": "Krakow",   "duration": 5},  # Workshop must be attended between day 5 and 9; day5 is in this block.
    {"name": "Frankfurt", "duration": 4},
    {"name": "Florence",  "duration": 2},
    {"name": "Munich",    "duration": 5},
    {"name": "Hamburg",   "duration": 5},
    {"name": "Oslo",      "duration": 5},
    {"name": "Vilnius",   "duration": 5},
    {"name": "Istanbul",  "duration": 5},  # Must contain days 25 to 29 (annual show); see below.
    {"name": "Stockholm", "duration": 3},
    {"name": "Santorini", "duration": 2}
]

# Calculate day ranges for each city.
# Using the formula:
# For i=0, start_day = 1.
# For i > 0, start_day = 1 + (sum of durations for cities 0 to i-1) - i.
# End_day = start_day + duration - 1.
itinerary = []
cumulative = 0
for i, city in enumerate(cities):
    if i == 0:
        start_day = 1
    else:
        start_day = 1 + cumulative - i  # subtract one for each flight overlap
    end_day = start_day + city["duration"] - 1
    itinerary.append({
        "day_range": f"{start_day}-{end_day}",
        "place": city["name"]
    })
    cumulative += city["duration"]

# At this point, the itinerary is computed.
# For clarity, the itinerary is:
# 1. Krakow:       days 1-5        (includes day 5, workshop satisfied)
# 2. Frankfurt:    days 5-8
# 3. Florence:     days 8-9
# 4. Munich:       days 9-13
# 5. Hamburg:      days 13-17
# 6. Oslo:         days 17-21
# 7. Vilnius:      days 21-25
# 8. Istanbul:     days 25-29     (includes days 25-29, annual show satisfied)
# 9. Stockholm:    days 29-31
# 10. Santorini:   days 31-32
#
# Total itinerary: 32 days.

# Output the itinerary as a JSON-formatted dictionary.
print(json.dumps(itinerary, indent=2))