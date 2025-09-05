import json

# Trip constraints
total_days = 15

# Required days in each city (including flight overlap)
required_days = {
    "Madrid": 7,     # Also hosts the annual show from Day 1 to Day 7
    "Paris": 6,
    "Seville": 3,
    "Bucharest": 2  # Visit relatives between Day 14 and Day 15
}

# Forced itinerary events:
# - Madrid: must be present on Days 1-7
# - Bucharest: must be present on Days 14-15

# Direct flights available between cities
direct_flights = [
    ("Paris", "Bucharest"),
    ("Seville", "Paris"),
    ("Madrid", "Bucharest"),
    ("Madrid", "Paris"),
    ("Madrid", "Seville")
]

def flight_available(city_a, city_b):
    """Return True if there is a direct flight between city_a and city_b."""
    return (city_a, city_b) in direct_flights or (city_b, city_a) in direct_flights

# We want to visit 4 cities:
#   - Madrid (Days 1-7, show attendance)
#   - Seville (3 days)
#   - Paris (6 days)
#   - Bucharest (Days 14-15, relatives visit)
#
# Based on the available direct flights, one valid route is:
# Madrid -> Seville -> Paris -> Bucharest
cities_chain = ["Madrid", "Seville", "Paris", "Bucharest"]

# Check that all required direct flights exist in our chosen chain.
for i in range(len(cities_chain) - 1):
    if not flight_available(cities_chain[i], cities_chain[i+1]):
        raise Exception("Direct flight not available between {} and {}".format(cities_chain[i], cities_chain[i+1]))

# To meet the overlapping flight day rules, we schedule transitions such that:
# - If a flight occurs on day X, that day counts for both the departure and arrival city.
#
# We already know:
#   Madrid must occupy Days 1-7.
#   Bucharest must be visited on Days 14-15.
#
# We now design the segments so that the overlapping flight days yield the needed total for each city:
#
# Let the flight from Madrid to Seville occur on Day 7.
#   -> Madrid: Days 1-7 (7 days total)
#
# For Seville (needs 3 days), we plan:
#   Arrival from Madrid on Day 7, spend full Day 8, and take the flight to Paris on Day 9.
#   -> Seville counts Day 7 (arrival), Day 8, and Day 9 (departure) = 3 days.
#
# For Paris (needs 6 days), we plan:
#   Arrival from Seville on Day 9, full Days 10-13, then fly to Bucharest on Day 14.
#   -> Paris counts Day 9 (arrival), Days 10, 11, 12, 13, and Day 14 (departure) = 6 days.
#
# For Bucharest (needs 2 days and must cover Days 14-15):
#   Arrival from Paris on Day 14 and stay through Day 15.
#   -> Bucharest counts Day 14 (arrival) and Day 15 = 2 days.

madrid_segment = (1, 7)       # Days 1 to 7 in Madrid
seville_segment = (7, 9)        # Days 7 to 9 in Seville (flight on Day 7 from Madrid and on Day 9 to Paris)
paris_segment = (9, 14)         # Days 9 to 14 in Paris (flight on Day 9 arrival and flight on Day 14 departure)
bucharest_segment = (14, 15)    # Days 14 to 15 in Bucharest

# Verify that the last day of Bucharest matches the overall trip length
if bucharest_segment[1] != total_days:
    raise Exception("The itinerary does not end on Day {} as required.".format(total_days))

# Build the itinerary list with day ranges and locations.
itinerary = [
    {
        "day_range": "Day {}-{}".format(madrid_segment[0], madrid_segment[1]),
        "place": "Madrid"
    },
    {
        "day_range": "Day {}-{}".format(seville_segment[0], seville_segment[1]),
        "place": "Seville"
    },
    {
        "day_range": "Day {}-{}".format(paris_segment[0], paris_segment[1]),
        "place": "Paris"
    },
    {
        "day_range": "Day {}-{}".format(bucharest_segment[0], bucharest_segment[1]),
        "place": "Bucharest"
    }
]

# The final result is output as a JSON-formatted dictionary.
result = {"itinerary": itinerary}
print(json.dumps(result))