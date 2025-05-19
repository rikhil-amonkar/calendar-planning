#!/usr/bin/env python3
import json

# Define the cities with their required durations (in days)
requirements = {
    "Paris": 2,
    "Krakow": 3,
    "Vienna": 4,
    "Riga": 4,
    "Hamburg": 2,
    "Barcelona": 2,
    "Edinburgh": 4,
    "Stockholm": 2
}

# Define the flight connectivity as a bidirectional graph.
flights = {
    "Hamburg": {"Stockholm", "Vienna", "Paris", "Barcelona", "Edinburgh", "Riga"},
    "Stockholm": {"Hamburg", "Vienna", "Edinburgh", "Krakow", "Barcelona", "Paris", "Riga"},
    "Vienna": {"Stockholm", "Hamburg", "Barcelona", "Krakow", "Paris", "Riga"},
    "Paris": {"Edinburgh", "Riga", "Krakow", "Hamburg", "Stockholm", "Barcelona", "Vienna"},
    "Riga": {"Barcelona", "Paris", "Edinburgh", "Stockholm", "Vienna", "Hamburg"},
    "Krakow": {"Barcelona", "Paris", "Stockholm", "Edinburgh", "Vienna"},
    "Barcelona": {"Riga", "Krakow", "Stockholm", "Edinburgh", "Hamburg", "Paris", "Vienna"},
    "Edinburgh": {"Paris", "Stockholm", "Krakow", "Hamburg", "Riga", "Barcelona"}
}

# Hardcoded itinerary order that meets all constraints based on analysis:
# Order chosen: Paris, Krakow, Vienna, Riga, Hamburg, Barcelona, Edinburgh, Stockholm
# Check that each consecutive pair has a direct flight.
itinerary_order = ["Paris", "Krakow", "Vienna", "Riga", "Hamburg", "Barcelona", "Edinburgh", "Stockholm"]

def valid_flights(order):
    for i in range(len(order)-1):
        city_from = order[i]
        city_to = order[i+1]
        if city_to not in flights.get(city_from, set()) and city_from not in flights.get(city_to, set()):
            return False
    return True

if not valid_flights(itinerary_order):
    raise Exception("The chosen itinerary order does not satisfy flight connectivity.")

# We assume no extra waiting days: each city is visited for exactly its required duration.
# The rule is: if flying from A to B on day X, then day X counts for both A and B.
# Let s[i] be the start day of city i.
# The recurrence: s[0] = start_day, and for i >= 1, s[i] = s[i-1] + (duration[A[i-1]] - 1)
# We want the overall trip to cover exactly 16 days.
# With the sum of required durations = 23 and 7 overlapping flight days, the total trip length is 23-7 = 16.
#
# We choose start_day such that the constraints are met:
#  - Wedding in Paris between day 1 and day 2: Paris day_range must include day 1 or day 2.
#  - Conference in Hamburg on days 10 and 11.
#  - A friend meeting in Edinburgh between day 12 and day 15.
#  - Relatives in Stockholm on days 15 and 16.
#
# After analysis, the following assignment works when using start_day = 1:
#
# City         Duration   Start   End (start + duration - 1)
# -----------------------------------------------------------
# Paris         2         1       2           --> Wedding in Paris (day 1-2 OK)
# Krakow        3         1+2-1 = 2       2+3-1 = 4   (days 2-4)
# Vienna        4         2+3-1 = 4       4+4-1 = 7   (days 4-7)
# Riga          4         4+4-1 = 7       7+4-1 = 10  (days 7-10)
# Hamburg       2         7+4-1 = 10      10+2-1 = 11 (days 10-11 --> Conference OK)
# Barcelona     2         10+2-1 = 11     11+2-1 = 12 (days 11-12)
# Edinburgh     4         11+2-1 = 12     12+4-1 = 15 (days 12-15 --> Friend meeting OK)
# Stockholm     2         12+4-1 = 15     15+2-1 = 16 (days 15-16 --> Relatives OK)
#
# Total trip covers days 1 through 16.
#
# Note: The flight rule means the departure day is shared.
start_day = 1
schedule = []
current_start = start_day

# Compute day ranges for each city in the itinerary order.
for city in itinerary_order:
    duration = requirements[city]
    end_day = current_start + duration - 1
    schedule.append({
        "day_range": f"{current_start}-{end_day}",
        "place": city
    })
    # Next city starts on the same day as the current city's end_day (overlap)
    current_start = end_day

# Now validate constraints on the scheduled day ranges:
def parse_range(day_range_str):
    start_str, end_str = day_range_str.split("-")
    return int(start_str), int(end_str)

# Constraint checks
def check_constraints(schedule):
    cons = []
    # Wedding in Paris between day 1 and day 2
    for seg in schedule:
        if seg["place"] == "Paris":
            s, e = parse_range(seg["day_range"])
            if not (s <= 1 <= e or s <= 2 <= e):
                cons.append("Wedding in Paris constraint not met")
    # Conference in Hamburg on day 10 and day 11
    for seg in schedule:
        if seg["place"] == "Hamburg":
            s, e = parse_range(seg["day_range"])
            if not (s <= 10 <= e and s <= 11 <= e):
                cons.append("Conference in Hamburg constraint not met")
    # Friend meeting in Edinburgh between day 12 and day 15 (at least one day in that interval)
    for seg in schedule:
        if seg["place"] == "Edinburgh":
            s, e = parse_range(seg["day_range"])
            if not (any(day in range(12, 16) for day in range(s, e+1))):
                cons.append("Friend meeting in Edinburgh constraint not met")
    # Relatives in Stockholm on day 15 and day 16
    for seg in schedule:
        if seg["place"] == "Stockholm":
            s, e = parse_range(seg["day_range"])
            if not (s <= 15 <= e and s <= 16 <= e):
                cons.append("Relatives in Stockholm constraint not met")
    return cons

constraints_fail = check_constraints(schedule)
if constraints_fail:
    raise Exception("Constraints not satisfied: " + ", ".join(constraints_fail))

# Output the schedule as a JSON-formatted dictionary (list of segments)
print(json.dumps(schedule, indent=2))