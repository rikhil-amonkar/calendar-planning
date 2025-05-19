#!/usr/bin/env python3
import json

# Input parameters (constraints and flight network)
total_days = 25

# Predefined cities with required stays, and special event day constraints:
# Each city duration is defined as the required number of days.
# Note: If a flight occurs on a day, that day counts to both the origin and destination.
constraints = {
    "Reykjavik": {
        "days": 4,
        "workshop": (1, 4),  # Must attend workshop between day 1 and 4
    },
    "Stuttgart": {
        "days": 4,
        "conference": [4, 7]  # Must attend conference on day 4 and day 7
    },
    "Valencia": {
        "days": 5,
    },
    "Seville": {
        "days": 3,
    },
    "Munich": {
        "days": 3,
        "annual_show": (13, 15)  # Must attend annual show between day 13 and 15
    },
    "Geneva": {
        "days": 5,
    },
    "Istanbul": {
        "days": 4,
        "relatives": (19, 22)  # Visit relatives between day 19 and 22
    },
    "Vilnius": {
        "days": 4,
    }
}

# Flight network (direct flights; note: flights are bidirectional unless specified otherwise)
# Each flight is represented as a tuple (cityA, cityB)
flights = [
    ("Geneva", "Istanbul"),
    ("Reykjavik", "Munich"),
    ("Stuttgart", "Valencia"),
    ("Reykjavik", "Stuttgart"),
    ("Stuttgart", "Istanbul"),
    ("Munich", "Geneva"),
    ("Istanbul", "Vilnius"),
    ("Valencia", "Seville"),
    ("Valencia", "Istanbul"),
    ("Vilnius", "Munich"),
    ("Seville", "Munich"),
    ("Munich", "Istanbul"),
    ("Valencia", "Geneva"),
    ("Valencia", "Munich")
]
# For our itinerary, we choose a route that obeys the flight network and the event constraints.

# Planned itinerary:
# We have to plan a sequence that covers 8 cities with direct flights.
# We choose the following ordering of visits along with flight days:
#
# 1. Reykjavik: days 1-4
#    => Contains the workshop (between day 1 and 4)
#
# Flight on day 4 from Reykjavik to Stuttgart (Reykjavik->Stuttgart exists)
#
# 2. Stuttgart: days 4-7
#    => Contains conferences on day 4 and day 7.
#
# Flight on day 7 from Stuttgart to Valencia (Stuttgart<->Valencia exists)
#
# 3. Valencia: days 7-11 (5 days as required)
#
# Flight on day 11 from Valencia to Seville (Valencia<->Seville exists)
#
# 4. Seville: days 11-13 (3 days required)
#
# Flight on day 13 from Seville to Munich (Seville<->Munich exists)
#
# 5. Munich: days 13-15 (3 days, and annual show on days 13-15)
#
# Flight on day 15 from Munich to Geneva (Munich<->Geneva exists)
#
# 6. Geneva: days 15-19 (5 days required)
#
# Flight on day 19 from Geneva to Istanbul (Geneva<->Istanbul exists)
#
# 7. Istanbul: days 19-22 (4 days required, and relatives between day 19 and 22)
#
# Flight on day 22 from Istanbul to Vilnius (Istanbul<->Vilnius exists)
#
# 8. Vilnius: days 22-25 (4 days required)
#
# Note: Each flight day is counted in both the departing city and the arrival city.
# This itinerary respects the overall 25-day framing (days 1 to 25).

# We now compute the day ranges based on the durations and flight overlap.
# Start at day 1.
day = 1
itinerary = []

# Helper function to create a day range string given start and end day.
def format_day_range(start, end):
    return f"{start}-{end}"

# 1. Reykjavik: days 1 to 4
start = day
end = start + constraints["Reykjavik"]["days"] - 1  # 4 days: 1-4
itinerary.append({
    "day_range": format_day_range(start, end),
    "place": "Reykjavik"
})
# Next flight: on the last day of Reykjavik (day 4) we also arrive at Stuttgart.
flight_day = end

# 2. Stuttgart: must be 4 days, already have day 4 included.
# so Stuttgart spans from day 4 to day 7.
start = flight_day  # overlapping day 4
end = start + constraints["Stuttgart"]["days"] - 1  # 4 days: 4,5,6,7
itinerary.append({
    "day_range": format_day_range(start, end),
    "place": "Stuttgart"
})
# Next flight: on last day (day 7) from Stuttgart to Valencia.
flight_day = end

# 3. Valencia: 5 days, starting on flight day overlapping day 7.
start = flight_day
end = start + constraints["Valencia"]["days"] - 1  # 7,8,9,10,11
itinerary.append({
    "day_range": format_day_range(start, end),
    "place": "Valencia"
})
# Next flight on day 11 from Valencia to Seville.
flight_day = end

# 4. Seville: 3 days, starting with overlap on day 11.
start = flight_day
end = start + constraints["Seville"]["days"] - 1  # 11,12,13
itinerary.append({
    "day_range": format_day_range(start, end),
    "place": "Seville"
})
# Next flight on day 13 from Seville to Munich.
flight_day = end

# 5. Munich: 3 days, starting on flight day (day 13)
start = flight_day
end = start + constraints["Munich"]["days"] - 1  # 13,14,15
itinerary.append({
    "day_range": format_day_range(start, end),
    "place": "Munich"
})
# Next flight on day 15 from Munich to Geneva.
flight_day = end

# 6. Geneva: 5 days, starting on flight day (day 15)
start = flight_day
end = start + constraints["Geneva"]["days"] - 1  # 15,16,17,18,19
itinerary.append({
    "day_range": format_day_range(start, end),
    "place": "Geneva"
})
# Next flight on day 19 from Geneva to Istanbul.
flight_day = end

# 7. Istanbul: 4 days, starting on flight day (day 19)
start = flight_day
end = start + constraints["Istanbul"]["days"] - 1  # 19,20,21,22
itinerary.append({
    "day_range": format_day_range(start, end),
    "place": "Istanbul"
})
# Next flight on day 22 from Istanbul to Vilnius.
flight_day = end

# 8. Vilnius: 4 days, starting on flight day (day 22)
start = flight_day
end = start + constraints["Vilnius"]["days"] - 1  # 22,23,24,25
itinerary.append({
    "day_range": format_day_range(start, end),
    "place": "Vilnius"
})

# Validate that the final day does not exceed total_days.
if end != total_days:
    raise ValueError(f"Total itinerary days ({end}) do not match expected {total_days}.")

# Output the itinerary as a JSON-formatted dictionary list containing only day_range and place.
print(json.dumps(itinerary, indent=2))