import json

# Input parameters
total_days = 12
cities = ["Vilnius", "Munich", "Mykonos"]

# Required days in each city (including flight overlap)
required_days = {
    "Vilnius": 4,
    "Munich": 3,
    "Mykonos": 7
}

# Direct flight connections available (used for feasibility checking, not for output):
# Direct flights exist: Vilnius -> Munich and Munich <-> Mykonos

# We note that when flying from one city to another on a given day, that day counts for both cities.
# Therefore, if we schedule flights in the order: Vilnius -> Munich -> Mykonos,
# the total days is: days_in_Vilnius + days_in_Munich + days_in_Mykonos - (# of flight days)
# where # of flight days = 2 in our itinerary.
# In our case:
# Total days = 4 + 3 + 7 - 2 = 12 which matches total_days.

# Compute itinerary:
itinerary = []
# Start with Vilnius from day 1
current_day = 1

# Vilnius itinerary: Day 1 to 4
vilnius_start = current_day
vilnius_end = vilnius_start + required_days["Vilnius"] - 1  # no flight before first city
itinerary.append({
    "day_range": f"{vilnius_start}-{vilnius_end}",
    "place": "Vilnius"
})

# Next, fly from Vilnius to Munich. Flight day is the last day of Vilnius.
# That day counts as Munich's first day.
current_day = vilnius_end  # flight day overlaps so Munich starts at the same day
munich_start = current_day
# Munich requires 3 days, but day munich_start is already counted,
# so additional days = 3 - 1.
munich_end = munich_start + required_days["Munich"] - 1
itinerary.append({
    "day_range": f"{munich_start}-{munich_end}",
    "place": "Munich"
})

# Next, fly from Munich to Mykonos. The flight day is the last day of Munich.
# That day counts as Mykonos' first day.
current_day = munich_end  # flight day overlaps so Mykonos starts at this day
mykonos_start = current_day
# Mykonos requires 7 days, but the flight day is already counted.
mykonos_end = mykonos_start + required_days["Mykonos"] - 1
itinerary.append({
    "day_range": f"{mykonos_start}-{mykonos_end}",
    "place": "Mykonos"
})

# Output the final itinerary as JSON-formatted dictionary
print(json.dumps(itinerary))