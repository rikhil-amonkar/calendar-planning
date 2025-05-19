import json

# Input Parameters (all durations in days)
total_trip_days = 23
# Required stays for each city
durations = {
    "Edinburgh": 5,
    "Amsterdam": 4,
    "Vienna": 5,
    "Reykjavik": 5,
    "Berlin": 4,
    "Brussels": 5
}
# Special constraint windows (inclusive)
constraints = {
    "Amsterdam": {"relatives": (5, 8)},   # Must be present at some point between day 5 and 8 in Amsterdam.
    "Reykjavik": {"workshop": (12, 16)},    # Must be present at some point between day 12 and 16 in Reykjavik.
    "Berlin": {"friend": (16, 19)}          # Must be present at some point between day 16 and 19 in Berlin.
}

# Direct flight network (bidirectional edges)
direct_flights = {
    "Edinburgh": {"Berlin", "Amsterdam", "Brussels"},
    "Amsterdam": {"Berlin", "Edinburgh", "Reykjavik", "Vienna"},
    "Berlin": {"Edinburgh", "Amsterdam", "Vienna", "Brussels", "Reykjavik"},
    "Brussels": {"Berlin", "Edinburgh", "Vienna", "Reykjavik"},
    "Vienna": {"Berlin", "Reykjavik", "Brussels", "Amsterdam"},
    "Reykjavik": {"Vienna", "Brussels", "Amsterdam", "Berlin"}
}

# We must choose an order of cities that satisfies both the flight connections and the scheduling constraints.
# One order that works is:
#   1. Edinburgh (5 days)
#   2. Amsterdam (4 days)  --> Amsterdam must be visited between day 5 and 8 so that relatives can be seen.
#   3. Vienna (5 days)      --> Direct flight from Amsterdam to Vienna exists.
#   4. Reykjavik (5 days)   --> Direct flight from Vienna to Reykjavik exists. Reykjavik will satisfy the workshop window of day12 to day16.
#   5. Berlin (4 days)      --> Direct flight from Reykjavik to Berlin exists. Berlin meets the friend window of day16 to19.
#   6. Brussels (5 days)    --> Direct flight from Berlin to Brussels exists.
itinerary_order = ["Edinburgh", "Amsterdam", "Vienna", "Reykjavik", "Berlin", "Brussels"]

# Check that each consecutive pair has a direct flight (if not, our chosen order would be invalid)
def validate_flight_path(order, flights):
    for i in range(len(order) - 1):
        city_a, city_b = order[i], order[i+1]
        if city_b not in flights[city_a]:
            return False, f"No direct flight between {city_a} and {city_b}."
    return True, "Valid flight path."

valid, msg = validate_flight_path(itinerary_order, direct_flights)
if not valid:
    raise ValueError(msg)

# Given the overlap rule (if flying on a day, that day is counted for both the departure and arrival cities),
# the sum of all required days (28) minus the overlap (one per flight, 5 flights) should equal the overall trip days (23).
total_required = sum(durations[city] for city in itinerary_order)
num_flights = len(itinerary_order) - 1
if total_required - num_flights != total_trip_days:
    raise ValueError("The given durations and overlaps do not match the total trip days.")

# Schedule the trip: We assign day ranges such that the flight day is the last day of the current city and the first day of the next city.
trip_plan = []
current_day = 1

for index, city in enumerate(itinerary_order):
    required = durations[city]
    # The segment's end day is computed so that the total days counted in city equals required.
    # Because the first day is current_day, and if a flight is taken out on the last day (except for the final city),
    # that day counts for both cities.
    # So, if we are not at the last city, then: segment_length = (end - current_day + 1) should equal required.
    end_day = current_day + required - 1
    # Append the scheduled range
    trip_plan.append({
        "day_range": f"{current_day}-{end_day}",
        "place": city
    })
    # For all but final city, the flight happens on the end_day.
    # The next city's start day is the same as the flight day.
    if index < len(itinerary_order) - 1:
        current_day = end_day  # Overlap the flight day

# Verify special constraints:
# Amsterdam relatives: must have at least one day in [5,8]
def check_constraint(day_range, window):
    start, end = map(int, day_range.split("-"))
    w_start, w_end = window
    # There is an overlap if start <= w_end and end >= w_start.
    return start <= w_end and end >= w_start

for city, reqs in constraints.items():
    for event, window in reqs.items():
        # Find the segment for that city.
        segment = next(item for item in trip_plan if item["place"] == city)
        if not check_constraint(segment["day_range"], window):
            raise ValueError(f"Constraint for {city} ({event}) is not satisfied with day range {segment['day_range']} and window {window}.")

# Final trip plan as JSON output.
print(json.dumps(trip_plan))