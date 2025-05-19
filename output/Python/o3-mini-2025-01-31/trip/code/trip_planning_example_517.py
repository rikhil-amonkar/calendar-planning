import json

# Input parameters
total_days = 19

# Cities and required durations (in days, note that flight days count twice)
# The required durations for visiting each city:
durations = {
    "Dubrovnik": 5,
    "Warsaw": 2,
    "Stuttgart": 7,  # Must include days 7 and 13 (conference days)
    "Bucharest": 6,  # Must include a wedding between day 1 and day 6
    "Copenhagen": 3
}

# Direct flight connectivity (undirected edges, as flights can be taken in either direction)
direct_flights = {
    "Warsaw": {"Copenhagen", "Stuttgart", "Bucharest"},
    "Copenhagen": {"Warsaw", "Stuttgart", "Bucharest", "Dubrovnik"},
    "Stuttgart": {"Copenhagen", "Warsaw"},
    "Bucharest": {"Copenhagen", "Warsaw"},
    "Dubrovnik": {"Copenhagen"}
}

# We must choose a sequence of the 5 cities such that:
#   - Each adjacent pair in the itinerary has a direct flight connection.
#   - The wedding in Bucharest happens between day 1 and day 6, so Bucharest must be visited at the beginning.
#   - The conference in Stuttgart occurs on days 7 and 13, which forces Stuttgart to be scheduled
#     as a contiguous block that covers both day 7 and day 13.
#
# One feasible order is:
#   1. Bucharest (6 days) [Wedding between day 1-6]
#   2. Warsaw (2 days)
#   3. Stuttgart (7 days) [Must include days 7 and 13 - so set it from day 7 to 13]
#   4. Copenhagen (3 days)
#   5. Dubrovnik (5 days)
#
# Check connectivity for adjacent pairs:
#   Bucharest -> Warsaw: direct flight exists.
#   Warsaw -> Stuttgart: direct flight exists.
#   Stuttgart -> Copenhagen: direct flight exists.
#   Copenhagen -> Dubrovnik: direct flight exists.
#
# In this plan, flights are taken on 'transition' days:
#   If we fly on a day, that day counts as being in both cities.
#   With 5 segments, there are 4 transition days.
#   Thus, total days if segments are summed is 6+2+7+3+5 = 23 days.
#   But overlapping on 4 flight days gives an overall trip length of 23 - 4 = 19 days.
#
# We now compute the day ranges for each segment.
# When transitioning, the flight day is the last day of the previous segment and simultaneously the first day of the next segment.

itinerary_order = ["Bucharest", "Warsaw", "Stuttgart", "Copenhagen", "Dubrovnik"]

# Verify that each adjacent city in the itinerary has a direct flight connection.
def check_connectivity(order, flights):
    for i in range(len(order) - 1):
        current_city = order[i]
        next_city = order[i + 1]
        if next_city not in flights[current_city]:
            return False
    return True

if not check_connectivity(itinerary_order, direct_flights):
    raise ValueError("No valid direct flight connections for the chosen itinerary order.")

# Compute the start and end days for each city segment.
# In each transition, the travel day is shared (overlap).
schedule = []
current_day = 1

for i, city in enumerate(itinerary_order):
    city_duration = durations[city]
    # If it's not the first segment, the start day is the same as the previous segment's ending day.
    # This reflects that the flight day counts for both segments.
    if i > 0:
        start_day = current_day  # This day is shared between the previous city (as end) and this city (as start)
    else:
        start_day = current_day
    # End day computed as start day plus the city's duration minus one.
    end_day = start_day + city_duration - 1
    schedule.append({"day_range": f"{start_day}-{end_day}", "place": city})
    # For the next segment, set the current_day to the end_day (overlapping flight day)
    current_day = end_day

# Validate that our overall trip length matches total_days
overall_trip_days = current_day
if overall_trip_days != total_days:
    raise ValueError(f"Computed overall trip days {overall_trip_days} do not match expected {total_days}.")

# Also, ensure that the conference requirement is met:
# Stuttgart must be visited on day 7 and day 13.
# Find Stuttgart in the schedule:
stuttgart_entry = next(item for item in schedule if item["place"] == "Stuttgart")
stuttgart_start, stuttgart_end = map(int, stuttgart_entry["day_range"].split('-'))
if not (stuttgart_start <= 7 <= stuttgart_end and stuttgart_start <= 13 <= stuttgart_end):
    raise ValueError("The Stuttgart segment does not include the required conference days 7 and 13.")

# Ensure that the wedding in Bucharest (between day 1 and day 6) is met:
bucharest_entry = next(item for item in schedule if item["place"] == "Bucharest")
bucharest_start, bucharest_end = map(int, bucharest_entry["day_range"].split('-'))
if not (bucharest_start <= 6 and bucharest_start <= 1 <= bucharest_end):
    # We assume the wedding occurs any day between day1 and day6 if Bucharest is visited early.
    raise ValueError("The Bucharest segment does not meet the wedding constraint between day 1 and day 6.")

# Output the result as a JSON formatted dictionary with only day_range and place.
print(json.dumps(schedule))