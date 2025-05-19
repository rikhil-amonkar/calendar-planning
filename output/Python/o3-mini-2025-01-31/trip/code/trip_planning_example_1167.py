#!/usr/bin/env python3
import json

# In this problem the trip is 21 days long.
# There are 8 cities with required durations, but due to overlapping flight days (the day of flight counts in both cities)
# the total "sum" of required days is more than 21.
#
# Our chosen ordering (which satisfies the direct-flight connections and all time‐window constraints) is:
#
#  1. Mykonos – Spend 4 days. 
#       Additional constraint: Must visit relatives in Mykonos between day 1 and day 4.
#  2. Naples – Spend 4 days.
#       (Direct flight from Mykonos to Naples is allowed.)
#  3. Istanbul – Spend 3 days.
#       Constraint: Meet a friend in Istanbul sometime between day 9 and 11.
#       (Direct flight from Naples to Istanbul is allowed.)
#  4. Venice – Spend 3 days.
#       (There is a direct flight between Istanbul and Venice.)
#  5. Dublin – Spend 5 days.
#       Constraint: An annual show in Dublin from day 11 to 15.
#       (A direct flight from Venice to Dublin is allowed.)
#  6. Frankfurt – Spend 3 days.
#       Constraint: Meet friends at Frankfurt between day 15 and 17.
#       (A direct flight from Dublin to Frankfurt is allowed.)
#  7. Krakow – Spend 4 days.
#       (A direct flight from Frankfurt to Krakow is allowed.)
#  8. Brussels – Spend 2 days.
#       (A direct flight from Krakow to Brussels is allowed.)
#
# Notice: The day-of-flight rule is that if you fly on a given day from city A to city B,
# that day counts for both cities. So when planning the itinerary, if a city is scheduled to
# have D days, its last day doubles as the arrival day of the next city.
#
# We can compute the start day of each city in the itinerary by:
#   s[0] = 1 (start day of first city)
#   for each subsequent city i:
#       s[i] = s[i-1] + duration[i-1] - 1
# and the trip will finish on:
#       finish = s[last] + duration[last] - 1
#
# With our chosen ordering, we have:
#   Mykonos (4 days), Naples (4), Istanbul (3), Venice (3), Dublin (5), Frankfurt (3), Krakow (4), Brussels (2)
#
# The computed schedule is:
#   s1 = 1
#   s2 = 1 + 4 - 1 = 4       -> Naples: days 4 to 7
#   s3 = 4 + 4 - 1 = 7       -> Istanbul: days 7 to 9
#   s4 = 7 + 3 - 1 = 9       -> Venice: days 9 to 11
#   s5 = 9 + 3 - 1 = 11      -> Dublin: days 11 to 15  (meets the show window exactly)
#   s6 = 11 + 5 - 1 = 15     -> Frankfurt: days 15 to 17 (meets the friend meeting window exactly)
#   s7 = 15 + 3 - 1 = 17     -> Krakow: days 17 to 20
#   s8 = 17 + 4 - 1 = 20     -> Brussels: days 20 to 21
#
# Note that all flight legs in this ordering have a corresponding direct-flight edge:
#   Mykonos <-> Naples, Naples <-> Istanbul, Istanbul <-> Venice, Venice <-> Dublin,
#   Dublin <-> Frankfurt, Frankfurt <-> Krakow, Krakow <-> Brussels.
#
# The itinerary meets these special requirements:
#   - Mykonos visit: days 1-4 (includes days 1 to 4 for relatives).
#   - Istanbul visit: days 7-9 (so day 9 is in Istanbul meeting window [9,11]).
#   - Dublin visit: days 11-15 (covering the annual show window exactly).
#   - Frankfurt visit: days 15-17 (covering the friend meeting window exactly).
#
# Finally, the last day of the trip is day 21.
#
# We output the itinerary as a list of dictionaries with keys "day_range" and "place".
# Only these keys are included in the JSON output.

# Define the itinerary as a list of tuples: (place, duration)
# The order is chosen to satisfy all constraints and direct flight rules.
itinerary = [
    ("Mykonos", 4),   # Relatives: Must have at least one day between day 1 and 4
    ("Naples", 4),
    ("Istanbul", 3),  # Friend meeting between day 9 and 11: day 9 qualifies
    ("Venice", 3),
    ("Dublin", 5),    # Annual show in Dublin from day 11 to 15: exactly matches when starting on day 11
    ("Frankfurt", 3), # Friends meeting in Frankfurt between day 15 and 17: exactly matches when starting on day 15
    ("Krakow", 4),
    ("Brussels", 2)
]

# Compute the start day for each city.
schedule = []
current_day = 1  # start day for the first city
for place, duration in itinerary:
    start_day = current_day
    end_day = start_day + duration - 1
    # Append a dictionary with day_range and place
    schedule.append({"day_range": f"{start_day}-{end_day}", "place": place})
    # Next city start day: overlap on the last day of current city.
    current_day = end_day

# The computed schedule:
# Mykonos: 1-4
# Naples: 4-7
# Istanbul: 7-9
# Venice: 9-11
# Dublin: 11-15
# Frankfurt: 15-17
# Krakow: 17-20
# Brussels: 20-21
#
# Final check of special constraints:
# - Mykonos visit (1-4) includes days 1-4, so relatives are visited in the proper window.
# - Istanbul visit (7-9) means day 9 is in Istanbul and meets the friend meeting window (9-11).
# - Dublin visit (11-15) exactly covers the annual show window.
# - Frankfurt visit (15-17) exactly covers the touring friends meeting window.
# Also, the total trip ends on day 21.

# Print final itinerary as JSON
print(json.dumps(schedule))