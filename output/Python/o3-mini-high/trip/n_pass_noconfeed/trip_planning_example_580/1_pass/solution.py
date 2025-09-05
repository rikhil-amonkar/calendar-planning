import json
import itertools

# Trip constraints
total_trip_days = 23

# Required stay durations (in days) for each city.
# Note: When flying between cities on a transition day, that day counts for both cities.
city_durations = {
    "Geneva": 7,      # Also required for conference on day1 and day7
    "Paris": 6,
    "Porto": 7,
    "Reykjavik": 2,
    "Oslo": 5         # Must include relatives visit between day 19 and day 23
}

# List of cities
cities = list(city_durations.keys())

# Flight connectivity (each flight is bidirectional)
# Represented as a set of frozensets (order independent)
allowed_flights = {
    frozenset(["Paris", "Oslo"]),
    frozenset(["Geneva", "Oslo"]),
    frozenset(["Porto", "Paris"]),
    frozenset(["Geneva", "Paris"]),
    frozenset(["Geneva", "Porto"]),
    frozenset(["Paris", "Reykjavik"]),
    frozenset(["Reykjavik", "Oslo"]),
    frozenset(["Porto", "Oslo"])
}

# Additional key constraints:
# - Conference in Geneva on day 1 and day 7: must start in Geneva so that day 1 is in Geneva and its 7-day stay covers day 7.
# - Relatives in Oslo between day 19 and day 23: must finish with Oslo.
start_city = "Geneva"
end_city = "Oslo"

# The remaining cities to schedule in between:
middle_cities = [city for city in cities if city not in [start_city, end_city]]

# Function to check if a proposed route is valid given the flight connections.
def is_valid_route(route, allowed_flights):
    for i in range(len(route) - 1):
        if frozenset([route[i], route[i+1]]) not in allowed_flights:
            return False
    return True

# Find a valid ordering for the itinerary given constraints.
# The itinerary must start with Geneva and end with Oslo.
valid_route = None
for perm in itertools.permutations(middle_cities):
    candidate = [start_city] + list(perm) + [end_city]
    if is_valid_route(candidate, allowed_flights):
        valid_route = candidate
        break

if not valid_route:
    print(json.dumps({"error": "No valid itinerary could be computed with the given flight connections."}))
    exit(1)

# Compute the itinerary day ranges.
# The logic: For the first city, start_day is day 1.
# For each subsequent city, the flight happens on the city's start day,
# meaning that the last day of the previous city is shared with the next city.
itinerary = []
current_day = 1

for city in valid_route:
    # The start day for the city segment.
    start_day = current_day
    # The city requires a given number of days.
    duration = city_durations[city]
    # The city segment ends on start_day + duration - 1.
    end_day = start_day + duration - 1
    itinerary.append({
        "day_range": f"Day {start_day}-{end_day}",
        "place": city
    })
    # For the next city, the flight occurs on the end_day (the shared day),
    # so we set current_day to end_day.
    current_day = end_day

# Validate total trip days
if current_day != total_trip_days:
    # This situation should not occur if the math adds up.
    print(json.dumps({"error": "Computed itinerary does not sum to total trip days."}))
    exit(1)

# Output the computed itinerary as a JSON-formatted dictionary.
result = {"itinerary": itinerary}
print(json.dumps(result))