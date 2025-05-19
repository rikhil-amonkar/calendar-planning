import json

# Input constraints (all durations are in days)
# Cities and required stay durations:
# Porto: 3 days (with workshop between day 1 and 3)
# Paris: 5 days
# Florence: 3 days
# Munich: 5 days
# Warsaw: 3 days (with wedding between day 13 and 15)
# Nice: 5 days
# Vienna: 2 days (with relatives visit between day 19 and 20)
#
# All flights are direct as per the network:
#   Porto <-> Paris, Paris <-> Florence, Florence -> Munich, Munich -> Warsaw,
#   Warsaw -> Nice, Nice -> Vienna, among other connections.
#
# The overlapping flight rule:
# If one flies from city A to city B on day X, then that day X counts for both cities.
#
# With 7 cities and 6 transitions, the effective total number of days is:
# sum(city_durations) - (number_of_transitions) = (3+5+3+5+3+5+2) - 6 = 26 - 6 = 20 days.

# We pre-define the itinerary order which respects the constraints:
# 1. Start in Porto (days 1-3) : workshop constraint (day 1 to day3)
# 2. Fly Porto -> Paris on day 3; Paris (days 3-7) : 5 days staying, flight on day 3 counted in both
# 3. Fly Paris -> Florence on day 7; Florence (days 7-9)
# 4. Fly Florence -> Munich on day 9; Munich (days 9-13)
# 5. Fly Munich -> Warsaw on day 13; Warsaw (days 13-15) : wedding falls between day 13 and day15
# 6. Fly Warsaw -> Nice on day 15; Nice (days 15-19)
# 7. Fly Nice -> Vienna on day 19; Vienna (days 19-20) : visit relatives between day 19 and day20

itinerary_cities = [
    ("Porto", 3),
    ("Paris", 5),
    ("Florence", 3),
    ("Munich", 5),
    ("Warsaw", 3),
    ("Nice", 5),
    ("Vienna", 2)
]

# Compute the day ranges using the overlapping flight rule:
# The start day of the first city is 1.
# For each subsequent city, its start day is the end day of the previous city.
result = []
current_day = 1

for city, duration in itinerary_cities:
    # The city is occupied from current_day to (current_day + duration - 1) inclusive.
    start_day = current_day
    end_day = current_day + duration - 1
    day_range = f"{start_day}-{end_day}"
    result.append({"day_range": day_range, "place": city})
    # For the next city, the flight happens on the end_day, so the next city starts that same day.
    current_day = end_day

# Validate the overall number of days:
# Since we double-count each flight day (6 transitions) the total unique days is:
# total_count = sum(durations) - (len(itinerary_cities) - 1)
total_unique_days = sum(duration for _, duration in itinerary_cities) - (len(itinerary_cities) - 1)
assert total_unique_days == 20, "Total days do not add up to 20."

# Additional check: ensure that Warsaw's range covers the wedding period (days 13-15)
warshaw_range = next((segment["day_range"] for segment in result if segment["place"] == "Warsaw"), None)
assert warshaw_range == "13-15", "Warsaw's day range must be 13-15 for the wedding."

# Additional check: ensure that Porto's range covers the workshop period (days 1-3)
porto_range = next((segment["day_range"] for segment in result if segment["place"] == "Porto"), None)
assert porto_range == "1-3", "Porto's day range must be 1-3 for the workshop."

# Additional check: ensure that Vienna's range covers the relative visit period (day 19 to 20)
vienna_range = next((segment["day_range"] for segment in result if segment["place"] == "Vienna"), None)
assert vienna_range == "19-20", "Vienna's day range must be 19-20 for the relative visit."

# Output the result as a JSON-formatted dictionary containing only the day ranges and places.
output = {"itinerary": result}
print(json.dumps(output))