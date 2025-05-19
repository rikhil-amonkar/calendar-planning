#!/usr/bin/env python3
import json

# Define input parameters (all durations in days, plus event time windows and flight connectivity)
total_days = 19

# Cities and required durations
durations = {
    "Tallinn": 2,     # friend meeting must happen between day 1 and 2, so this must be first.
    "Prague": 3,      
    "Lisbon": 2,      # workshop event between day 4 and 5 must occur in Lisbon
    "Copenhagen": 5,  
    "Dubrovnik": 5,   
    "Stockholm": 4,   # wedding between day 13 and 16 must occur in Stockholm
    "Split": 3,       
    "Lyon": 2        # annual show between day 18 and 19 must occur in Lyon
}

# Direct flight connections among cities (bidirectional)
flights = {
    ("Dubrovnik", "Stockholm"),
    ("Lisbon", "Copenhagen"),
    ("Lisbon", "Lyon"),
    ("Copenhagen", "Stockholm"),
    ("Copenhagen", "Split"),
    ("Prague", "Stockholm"),
    ("Tallinn", "Stockholm"),
    ("Prague", "Lyon"),
    ("Lisbon", "Stockholm"),
    ("Prague", "Lisbon"),
    ("Stockholm", "Split"),
    ("Prague", "Copenhagen"),
    ("Split", "Lyon"),
    ("Copenhagen", "Dubrovnik"),
    ("Prague", "Split"),
    ("Tallinn", "Copenhagen"),
    ("Tallinn", "Prague")
}
# Function to check if a direct flight exists between two cities
def can_fly(city_a, city_b):
    return (city_a, city_b) in flights or (city_b, city_a) in flights

# We now compute a valid itinerary order that meets all constraints.
# From the constraints we note:
# - Tallinn must be visited on day 1-2 (friend meeting window) -> so it must be first.
# - Lisbon must host the workshop on day 4-5 -> Lisbon must be visited such that its day range 
#   covers day 4 or day 5.
# - Stockholm must cover day 13-16 (wedding) and Lyon must cover day 18-19 (annual show).
#
# One valid itinerary order found by logical deduction is:
# 1. Tallinn (2 days)  [days 1-2]
# 2. Prague (3 days)   [flight on day 2, itinerary day range 2-4]
# 3. Lisbon (2 days)   [flight on day 4, itinerary day range 4-5]
# 4. Copenhagen (5 days) [flight on day 5, itinerary day range 5-9]
# 5. Dubrovnik (5 days)  [flight on day 9, itinerary day range 9-13]
# 6. Stockholm (4 days)  [flight on day 13, itinerary day range 13-16]
# 7. Split (3 days)      [flight on day 16, itinerary day range 16-18]
# 8. Lyon (2 days)       [flight on day 18, itinerary day range 18-19]
#
# Check flight connectivity between consecutive cities.
itinerary_order = ["Tallinn", "Prague", "Lisbon", "Copenhagen", "Dubrovnik", "Stockholm", "Split", "Lyon"]
for i in range(len(itinerary_order) - 1):
    if not can_fly(itinerary_order[i], itinerary_order[i+1]):
        raise ValueError(f"No direct flight between {itinerary_order[i]} and {itinerary_order[i+1]}")

# Now, assign day ranges taking into account that if a flight happens on day X, then on day X
# both the departure and arrival cities are counted.
# The rule: For the first city, the itinerary starts on day 1. For subsequent cities, the start day is the ending day of the previous city.
# And the "length" of the stay for city_i is the specified duration.
# So if the previous city's range was [start_prev, end_prev],
# then current city's range is [end_prev, end_prev + duration - 1]
# This ensures that one day (end_prev) is shared by both cities.
itinerary = []
current_day = 1
# Process the first city separately.
first_city = itinerary_order[0]
first_duration = durations[first_city]
# For the first city, the days range is 1 to first_duration (since no previous overlap is necessary)
itinerary.append({
    "day_range": f"{current_day}-{current_day + first_duration - 1}",
    "place": first_city
})
current_day = current_day + first_duration  # The next city will start on the last day of previous city

# Process subsequent cities
for city in itinerary_order[1:]:
    dur = durations[city]
    # The city's range starts at current_day (which is the same as the last city’s end day)
    start = current_day
    end = start + dur - 1
    itinerary.append({
        "day_range": f"{start}-{end}",
        "place": city
    })
    current_day = end  # Next city starts on this end day

# Verify that the itinerary covers the overall required days:
if current_day != total_days:
    raise ValueError(f"Itinerary total days {current_day} does not match required {total_days}")

# Check event constraints manually:
# Tallinn friend meeting: should occur between day 1 and day 2.
tallinn_range = itinerary[0]["day_range"]
tallinn_start, tallinn_end = map(int, tallinn_range.split('-'))
if not (tallinn_start <= 1 <= tallinn_end and tallinn_start <= 2 <= tallinn_end):
    raise ValueError("Tallinn does not satisfy the friend meeting window.")

# Lisbon workshop between day 4 and day 5.
lisbon_range = [item["day_range"] for item in itinerary if item["place"] == "Lisbon"][0]
lisbon_start, lisbon_end = map(int, lisbon_range.split('-'))
if not (lisbon_start <= 4 <= lisbon_end or lisbon_start <= 5 <= lisbon_end):
    raise ValueError("Lisbon does not satisfy the workshop window.")

# Stockholm wedding between day 13 and day 16.
stockholm_range = [item["day_range"] for item in itinerary if item["place"] == "Stockholm"][0]
stockholm_start, stockholm_end = map(int, stockholm_range.split('-'))
if not (stockholm_start <= 13 <= stockholm_end or stockholm_start <= 16 <= stockholm_end):
    raise ValueError("Stockholm does not satisfy the wedding window.")

# Lyon annual show from day 18 to day 19.
lyon_range = [item["day_range"] for item in itinerary if item["place"] == "Lyon"][0]
lyon_start, lyon_end = map(int, lyon_range.split('-'))
if not (lyon_start <= 18 <= lyon_end and lyon_start <= 19 <= lyon_end):
    raise ValueError("Lyon does not satisfy the annual show window.")

# Output the itinerary as a JSON-formatted dictionary containing only day_range and place.
print(json.dumps(itinerary, indent=4))