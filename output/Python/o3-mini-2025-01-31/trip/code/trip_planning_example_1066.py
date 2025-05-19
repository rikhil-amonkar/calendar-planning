import json

# Input parameters as provided in the problem statement:

# Total trip days
total_days = 21

# Cities and required durations when “staying” there.
# Note: if a flight is taken on a given day then that day counts for both
# the city you are leaving and the city you are arriving.
cities = {
    "Brussels": 4,
    "Bucharest": 3,
    "Stuttgart": 4,  # Also friend meeting requirement between day 1 and 4
    "Mykonos": 2,
    "Madrid": 2,     # And on day 20-21 (the conference)
    "Helsinki": 5,
    "Split": 3,
    "London": 5
}

# Direct flight network as bidirectional pairs.
flights = {
    "Helsinki": ["London", "Madrid", "Brussels", "Split"],
    "London": ["Helsinki", "Madrid", "Brussels", "Bucharest", "Stuttgart", "Split", "Mykonos"],
    "Split": ["Madrid", "Helsinki", "London", "Stuttgart"],
    "Madrid": ["Split", "Helsinki", "London", "Brussels", "Bucharest", "Mykonos"],
    "Brussels": ["London", "Bucharest", "Madrid", "Helsinki"],
    "Bucharest": ["London", "Brussels", "Madrid"],
    "Stuttgart": ["London", "Split"],
    "Mykonos": ["Madrid", "London"]
}

# We know from the problem constraints that:
# - Stuttgart must be encountered early, with the friend meeting between day 1 and 4.
# - Madrid must include days 20 and 21 (conference).
#
# We need to plan an itinerary (a Hamiltonian path covering the 8 cities)
# that obeys direct flight connectivity.
#
# After reviewing connections, one valid ordering is:
#   1. Stuttgart
#   2. Split
#   3. Helsinki
#   4. Brussels
#   5. Bucharest
#   6. London
#   7. Mykonos
#   8. Madrid
#
# Check connectivity:
#   Stuttgart -> Split         (direct flight exists)
#   Split -> Helsinki          (direct flight exists)
#   Helsinki -> Brussels       (direct flight exists)
#   Brussels -> Bucharest      (direct flight exists)
#   Bucharest -> London        (direct flight exists)
#   London -> Mykonos          (direct flight exists)
#   Mykonos -> Madrid          (direct flight exists)

itinerary_order = [
    "Stuttgart",
    "Split",
    "Helsinki",
    "Brussels",
    "Bucharest",
    "London",
    "Mykonos",
    "Madrid"
]

# Verify flight connectivity:
def valid_itinerary(order, flights):
    for i in range(len(order) - 1):
        if order[i+1] not in flights[order[i]]:
            return False
    return True

if not valid_itinerary(itinerary_order, flights):
    raise ValueError("Selected itinerary ordering does not obey the flight connectivity constraints.")

# Now, we compute the day ranges.
#
# Scheduling logic:
#   For the first city, assign its full duration from day 1.
#   For each flight (transition between cities), the flight day is an overlap day:
#       meaning the arrival day in the new city is the same day as the flight,
#       and that day is counted as a day in both cities.
#
# So, if d_i is the required duration in city i, then the unique days used across the whole itinerary is:
#   d_0 + sum(d_i - 1, for i = 1 to n-1) = total_days.
#
# Our totals:
#   Sum(durations) = 4+3+5+4+3+5+2+2 = 28.
#   Subtract overlaps (7 flights) gives 21 days.
#
# We set:
#   city0: start = 1, end = start + d0 - 1.
#   for each subsequent city: start = previous city's end (overlap day),
#   end = start + duration - 1.
#
# Verify that final end equals total_days.
schedule = []
current_day = 1

for idx, city in enumerate(itinerary_order):
    duration = cities[city]
    # For first city, no overlap adjustment
    if idx == 0:
        start_day = current_day
        end_day = start_day + duration - 1
    else:
        # Overlap: the flight day (which is the previous city's end day) counts for this city.
        start_day = current_day  # current_day is the previous city's end day.
        end_day = start_day + duration - 1
    schedule.append({
        "day_range": f"{start_day}-{end_day}",
        "place": city
    })
    current_day = end_day  # next city's start day will be this end_day (overlap day)

# Finally, verify the final day is total_days.
if current_day != total_days:
    raise ValueError(f"Computed itinerary lasts {current_day} days, expected {total_days} days.")

# Output the itinerary as a JSON-formatted dictionary (list of dictionaries)
print(json.dumps(schedule, indent=2))