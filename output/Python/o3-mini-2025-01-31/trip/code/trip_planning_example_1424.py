#!/usr/bin/env python3
import json

# Input parameters (durations and event windows)
# Durations for each city (in days, counting full, with transitions overlapping):
# Note: The overlapping flight rule makes total individual durations sum to 36,
# while the trip spans 27 calendar days (since 9 overlapping days are counted in two cities).
durations = {
    "Porto": 5,       # with a workshop event between day 1 and day 5
    "Amsterdam": 4,   # with a relatives visit event between day 5 and day 8
    "Helsinki": 4,    # with a wedding event between day 8 and day 11
    "Reykjavik": 5,
    "Warsaw": 3,
    "Naples": 4,      # with a conference event between day 17 and day 20
    "Brussels": 3,    # with an annual show event between day 20 and day 22
    "Valencia": 2,
    "Lyon": 3,
    "Split": 3
}

# The available direct flight connections (bidirectional)
direct_flights = {
    "Amsterdam": {"Warsaw", "Lyon", "Naples", "Reykjavik", "Split", "Helsinki", "Valencia"},
    "Warsaw": {"Amsterdam", "Split", "Valencia", "Brussels", "Naples", "Helsinki", "Porto"},
    "Helsinki": {"Brussels", "Warsaw", "Split", "Naples", "Reykjavik", "Amsterdam"},
    "Reykjavik": {"Brussels", "Warsaw", "Amsterdam", "Helsinki"},
    "Porto": {"Brussels", "Amsterdam", "Lyon", "Warsaw", "Valencia"},
    "Naples": {"Amsterdam", "Valencia", "Split", "Brussels", "Warsaw", "Helsinki"},
    "Brussels": {"Helsinki", "Reykjavik", "Porto", "Lyon", "Valencia", "Warsaw", "Naples"},
    "Split": {"Amsterdam", "Lyon", "Warsaw", "Naples", "Helsinki"},
    "Lyon": {"Amsterdam", "Split", "Brussels", "Porto", "Valencia"},
    "Valencia": {"Naples", "Brussels", "Lyon", "Porto", "Amsterdam", "Warsaw"}
}

# We need to choose an itinerary order that:
# (a) Visits all 10 cities exactly once
# (b) Uses only direct flights to go from one to the next
# (c) Meets the fixed event date constraints:
#     - Porto must be visited in the first segment so that its 5-day period covers a workshop between day 1 and 5.
#     - Amsterdam must include a relatives visit between day 5 and 8.
#     - Helsinki must include a wedding between day 8 and 11.
#     - Naples must include a conference between day 17 and 20.
#     - Brussels must include an annual show between day 20 and 22.
#
# By design, the overlapping flight-day rule implies:
#   s1 = 1, e1 = s1 + dur1 - 1.
#   For i > 1, s_i = e_(i-1) and e_i = s_i + dur_i - 1.
# The total trip finishes on day e_10 which must be 27.
#
# After some analysis, one itinerary that fits all these constraints and also respects direct flights is:
# Order:
# 1. Porto (5 days)         : day 1 to 5    (Workshop can be on day 3)
# 2. Amsterdam (4 days)      : day 5 to 8    (Relatives visit between day 5 and 8)
# 3. Helsinki (4 days)       : day 8 to 11   (Wedding between day 8 and 11)
# 4. Reykjavik (5 days)      : day 11 to 15
# 5. Warsaw (3 days)         : day 15 to 17
# 6. Naples (4 days)         : day 17 to 20  (Conference between day 17 and 20)
# 7. Brussels (3 days)       : day 20 to 22  (Annual show from day 20 to 22)
# 8. Valencia (2 days)       : day 22 to 23
# 9. Lyon (3 days)           : day 23 to 25
# 10. Split (3 days)         : day 25 to 27
#
# Check flight connectivity between consecutive cities:
#   Porto -> Amsterdam (exists: Porto-Amsterdam)
#   Amsterdam -> Helsinki (exists: Amsterdam-Helsinki)
#   Helsinki -> Reykjavik (exists: Helsinki-Reykjavik)
#   Reykjavik -> Warsaw (exists: Reykjavik-Warsaw)
#   Warsaw -> Naples (exists: Warsaw-Naples)
#   Naples -> Brussels (exists: Naples-Brussels)
#   Brussels -> Valencia (exists: Brussels-Valencia)
#   Valencia -> Lyon (exists: Valencia-Lyon)
#   Lyon -> Split (exists: Lyon-Split)
#
# With these segments, the overall timeline is 27 days.

# The itinerary order and durations (with computed day ranges)
itinerary_order = [
    "Porto",
    "Amsterdam",
    "Helsinki",
    "Reykjavik",
    "Warsaw",
    "Naples",
    "Brussels",
    "Valencia",
    "Lyon",
    "Split"
]

# Build the itinerary with day ranges:
itinerary = []
current_start = 1
for city in itinerary_order:
    d = durations[city]
    # end day is start + duration - 1
    current_end = current_start + d - 1
    # Append the itinerary info; day_range as "start-end"
    itinerary.append({
        "day_range": f"{current_start}-{current_end}",
        "place": city
    })
    # The next city starts on the same day as the current city ends (flight day counts in both)
    current_start = current_end

# The final day of the trip should be 27 according to the constraints.
assert itinerary[-1]["day_range"].split("-")[1] == "27", "Total trip days must be 27."

# Output the itinerary as JSON (only day_range and place for each city)
print(json.dumps(itinerary, indent=2))