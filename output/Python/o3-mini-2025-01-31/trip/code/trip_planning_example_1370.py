#!/usr/bin/env python3
import json

# Input parameters: cities, durations (required days), and specific day-constraints boundaries.
# Note: When flying from one city to the next on a transition day, that day counts for both cities.
#
# City durations (required days without counting flight overlaps):
#   Santorini: 5 days, must include a meet-with-friend day between 25 and 29.
#   Krakow:    5 days, wedding between 18 and 22.
#   Paris:     5 days, friend meeting between 11 and 15.
#   Vilnius:   3 days.
#   Munich:    5 days.
#   Geneva:    2 days.
#   Amsterdam: 4 days.
#   Budapest:  5 days.
#   Split:     4 days.
#
# There are 9 cities and the effective trip length is:
#   sum(required_days) - (number of transitions) = 38 - 8 = 30 days.
#
# We must choose an itinerary order that obeys:
#   (a) The day-range constraints (Paris block's span includes a day between 11 and 15,
#       Krakow block’s span includes a day between 18 and 22,
#       Santorini block’s span includes a day between 25 and 29).
#   (b) Flight connectivity given by the following direct flight links:
#       • Vilnius -> Munich       (from Vilnius to Munich)
#       • Munich <-> Paris        (Munich and Paris)
#       • Paris <-> Budapest      (Budapest and Paris)
#       • Budapest <-> Amsterdam  (Budapest and Amsterdam)
#       • Amsterdam <-> Krakow    (Krakow and Amsterdam)
#       • Krakow <-> Split        (Split and Krakow)
#       • Split <-> Geneva        (Split and Geneva)
#       • Geneva <-> Santorini    (Santorini and Geneva)
#
# One order satisfying both the connection and the time constraints is:
#   1. Vilnius (3 days)
#   2. Munich (5 days)
#   3. Paris (5 days)        --> Its span will be arranged to include day 11 (friend meeting).
#   4. Budapest (5 days)     --> Paris -> Budapest is allowed.
#   5. Amsterdam (4 days)    --> Budapest -> Amsterdam is allowed.
#   6. Krakow (5 days)       --> Amsterdam -> Krakow is allowed; Krakow block will cover day 18.
#   7. Split (4 days)        --> Krakow -> Split is allowed.
#   8. Geneva (2 days)       --> Split -> Geneva is allowed.
#   9. Santorini (5 days)    --> Geneva -> Santorini is allowed; block covers days 26-30 including days 26–29.
#
# The itinerary day assignment is computed by the following rule:
#   For city i (1-indexed), let required duration = D.
#   If it is the first city, assign day_range: [1, D].
#   For every subsequent city, the start day equals the previous city’s end day 
#   (inclusively, since the day of the flight counts in both cities), and the end day
#   equals start_day + (D - 1).
#
# With this rule, the overall trip (9 cities, 8 flight overlaps) has total days = sum(durations) - 8 = 38 - 8 = 30.
#
# Let’s compute the schedule:
cities = [
    {"name": "Vilnius",   "days": 3},
    {"name": "Munich",    "days": 5},
    {"name": "Paris",     "days": 5},  # Must cover friend meeting between day11 and day15.
    {"name": "Budapest",  "days": 5},  # Paris -> Budapest flight (allowed via Budapest and Paris).
    {"name": "Amsterdam", "days": 4},  # Budapest -> Amsterdam (allowed via Budapest and Amsterdam).
    {"name": "Krakow",    "days": 5},  # Wedding between day18 and day22 must fall in this block.
    {"name": "Split",     "days": 4},  # Krakow -> Split (allowed via Split and Krakow).
    {"name": "Geneva",    "days": 2},  # Split -> Geneva (allowed via Split and Geneva).
    {"name": "Santorini", "days": 5}   # Geneva -> Santorini (allowed via Santorini and Geneva).
]

schedule = []
current_start = 1

# For each city in the itinerary, compute the day range.
for city in cities:
    # The city block lasts exactly city["days"] days.
    start_day = current_start
    end_day = start_day + city["days"] - 1
    schedule.append({"day_range": f"{start_day}-{end_day}", "place": city["name"]})
    # For next city, the start is the same as the current end day (flight day overlap).
    current_start = end_day

# Validate key constraints (for debugging purposes, not included in output):
# Paris must include a day between 11 and 15.
for entry in schedule:
    if entry["place"] == "Paris":
        start, end = map(int, entry["day_range"].split("-"))
        if not (start <= 11 <= end or start <= 15 <= end or (11 >= start and 15 <= end)):
            raise ValueError("Paris block does not cover friend meeting days between 11 and 15.")
# Krakow must include a day between 18 and 22.
for entry in schedule:
    if entry["place"] == "Krakow":
        start, end = map(int, entry["day_range"].split("-"))
        # Check if there is an overlap with the wedding window.
        # We require that at least one day in [18,22] is within [start, end].
        if end < 18 or start > 22:
            raise ValueError("Krakow block does not cover wedding days between 18 and 22.")
# Santorini must include a day between 25 and 29.
for entry in schedule:
    if entry["place"] == "Santorini":
        start, end = map(int, entry["day_range"].split("-"))
        if end < 25 or start > 29:
            raise ValueError("Santorini block does not cover friend meeting days between 25 and 29.")

# Output the schedule as a JSON-formatted dictionary (list of dictionaries).
print(json.dumps(schedule))