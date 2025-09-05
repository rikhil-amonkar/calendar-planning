import itertools
import json

# Trip constraints as input variables
total_trip_days = 16
city_durations = {
    "Istanbul": 2,
    "Rome": 3,
    "Seville": 4,
    "Naples": 7,
    "Santorini": 4
}

# Special day constraints:
# Must be in Istanbul on a day between 6 and 7 (inclusive) to visit relatives.
istanbul_special_days = {6, 7}
# Must be in Santorini on at least one day between 13 and 16 (inclusive) for the wedding.
santorini_wedding_range = set(range(13, 17))

# Direct flight network (bidirectional flights)
allowed_flights = {
    frozenset({"Rome", "Santorini"}),
    frozenset({"Seville", "Rome"}),
    frozenset({"Istanbul", "Naples"}),
    frozenset({"Naples", "Santorini"}),
    frozenset({"Rome", "Naples"}),
    frozenset({"Rome", "Istanbul"})
}

# List of cities to visit
cities = list(city_durations.keys())  # Order comes from the dictionary definition

def compute_schedule(order):
    """
    Given an ordering of cities, compute the itinerary schedule.
    When flying from one city to the next, the flight day is shared.
    Each segment is represented by a tuple: (city, start_day, end_day)
    """
    schedule = []
    start_day = 1
    for city in order:
        duration = city_durations[city]
        end_day = start_day + duration - 1
        schedule.append((city, start_day, end_day))
        # Overlap the flight day: next city starts on the same day this city ends.
        start_day = end_day
    return schedule

def check_flight_connectivity(order):
    """
    Check that every flight from one city in the order to the next uses a direct flight.
    """
    for i in range(len(order) - 1):
        if frozenset({order[i], order[i+1]}) not in allowed_flights:
            return False
    return True

def check_special_constraints(schedule):
    """
    Verify that Istanbul's segment covers day 6 or 7 
    and Santorini's segment overlaps with wedding days 13-16.
    """
    for city, start, end in schedule:
        if city == "Istanbul":
            # Istanbul segment must include at least one of day 6 or 7.
            if not any(day in range(start, end + 1) for day in istanbul_special_days):
                return False
        if city == "Santorini":
            # Santorini segment must overlap with at least one wedding day (13-16).
            if not (end >= 13 and start <= 16):
                return False
    return True

valid_schedule = None

# Search over all permutations of cities that satisfy the flight connectivity and special constraints.
for permutation in itertools.permutations(cities):
    order = list(permutation)
    if not check_flight_connectivity(order):
        continue
    schedule = compute_schedule(order)
    # With the given durations and flight overlaps, the itinerary always ends on day = (sum(durations) - (#transitions))
    # We check if the overall trip matches the total_trip_days.
    if schedule[-1][2] != total_trip_days:
        continue
    if not check_special_constraints(schedule):
        continue
    valid_schedule = schedule
    break

# Format the output itinerary as a JSON dictionary.
if valid_schedule:
    itinerary = []
    for city, start, end in valid_schedule:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result))