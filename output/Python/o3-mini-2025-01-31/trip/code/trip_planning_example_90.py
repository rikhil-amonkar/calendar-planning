import json

# Input parameters
total_days = 17

# Cities and the required stay durations (noting that flight days count for both cities)
stay_naples = 5
stay_vienna = 7
stay_vilnius = 7

# Flight connections:
# Naples <-> Vienna, Vienna <-> Vilnius.
# We must have an itinerary that uses only these flights.

# Additional constraints:
# - Visit relatives in Naples between day 1 and day 5 (inclusive), so Naples must be visited from the start.
# - Since there is no direct flight between Naples and Vilnius, the only valid order is:
#   Naples --> Vienna --> Vilnius.
#
# Also note:
# If one flies on a transition day then that day counts in both the origin and destination.
#
# Let d1 be the flight day from Naples to Vienna.
# Then days in Naples = d1 (since day d1 counts as Naples as well).
# We need d1 = stay_naples = 5.
#
# Let d2 be the flight day from Vienna to Vilnius.
# Then days in Vienna = (d2 - d1 + 1) [because day d1 counts in Vienna (arrival day)]
# We require d2 - 5 + 1 = 7, so d2 = 11.
#
# Days in Vilnius = total_days - d2 + 1 = 17 - 11 + 1 = 7.
#
# This perfectly satisfies the required durations and total days.

flight_day_naples_vienna = stay_naples  # day 5
flight_day_vienna_vilnius = flight_day_naples_vienna + stay_vienna - 1  # day 11

# Construct the itinerary segments.
# Each segment is represented as a dictionary with "day_range" and "place"
itinerary = []

# Segment 1: Naples from day 1 to day 5
naples_day_start = 1
naples_day_end = flight_day_naples_vienna  # 5
itinerary.append({
    "day_range": f"{naples_day_start}-{naples_day_end}",
    "place": "Naples"
})

# Segment 2: Vienna from day 5 to day 11
vienna_day_start = flight_day_naples_vienna  # 5 (flight day counts for both Naples and Vienna)
vienna_day_end = flight_day_vienna_vilnius  # 11
itinerary.append({
    "day_range": f"{vienna_day_start}-{vienna_day_end}",
    "place": "Vienna"
})

# Segment 3: Vilnius from day 11 to day 17
vilnius_day_start = flight_day_vienna_vilnius  # 11 (flight day counts for both Vienna and Vilnius)
vilnius_day_end = total_days  # 17
itinerary.append({
    "day_range": f"{vilnius_day_start}-{vilnius_day_end}",
    "place": "Vilnius"
})

# Output the itinerary as a JSON-formatted dictionary
print(json.dumps(itinerary))