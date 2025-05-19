import json

# Input parameters (constraints)
total_days = 14
cities = ["Vienna", "Lyon", "Amsterdam", "Santorini"]

# Required durations in each city
durations = {
    "Vienna": 7,
    "Lyon": 3,
    "Amsterdam": 3,
    "Santorini": 4
}

# Event constraints:
# - Workshop in Amsterdam must occur between day 9 and day 11.
# - Wedding in Lyon must occur between day 7 and day 9.
# We design an itinerary such that:
#   Segment 1: Vienna for 7 days (days 1-7)
#   Segment 2: Lyon for 3 days (flight on day 7; days 7-9)
#   Segment 3: Amsterdam for 3 days (flight on day 9; days 9-11)
#   Segment 4: Santorini for 4 days (flight on day 11; days 11-14)
#
# Explanation: When flying from one city to the next on a flight day, that day is counted in both cities.
# Thus, the total days will be: (7 + 3 + 3 + 4) - 3 (overlap days) = 14.
#
# The flight legs are:
#   Vienna -> Lyon (direct available)
#   Lyon -> Amsterdam (direct available)
#   Amsterdam -> Santorini (direct available)

itinerary = []
current_day = 1

# Segment 1: Vienna - days 1 to 7
city = "Vienna"
start_day = current_day
end_day = start_day + durations[city] - 1  # no overlap at the very start
itinerary.append({"day_range": f"{start_day}-{end_day}", "place": city})
current_day = end_day  # current_day becomes the overlap day for flight

# Segment 2: Lyon - 3 days; flight on current_day so overlapping day included.
city = "Lyon"
start_day = current_day  # overlapping flight day with previous segment (day 7)
end_day = start_day + durations[city] - 1
itinerary.append({"day_range": f"{start_day}-{end_day}", "place": city})
current_day = end_day  # current_day becomes the overlap day for next flight

# Segment 3: Amsterdam - 3 days; flight on current_day so overlapping day included.
city = "Amsterdam"
start_day = current_day  # overlapping flight day (day 9)
end_day = start_day + durations[city] - 1
itinerary.append({"day_range": f"{start_day}-{end_day}", "place": city})
current_day = end_day  # current_day becomes the overlap day for next flight

# Segment 4: Santorini - 4 days; flight on current_day so overlapping day included.
city = "Santorini"
start_day = current_day  # overlapping flight day (day 11)
end_day = start_day + durations[city] - 1
itinerary.append({"day_range": f"{start_day}-{end_day}", "place": city})

# Check total days calculated: It should equal total_days
# Total days = sum(durations) - number of flights (3)
calculated_total = sum(durations.values()) - 3
if calculated_total != total_days:
    raise ValueError("The computed itinerary does not fit into the total days available.")

# Output the itinerary as a JSON-formatted dictionary (list of segments)
print(json.dumps(itinerary, indent=2))