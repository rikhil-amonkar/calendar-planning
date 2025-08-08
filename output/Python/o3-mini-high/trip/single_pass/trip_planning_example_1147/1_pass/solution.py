#!/usr/bin/env python3
import itertools
import json

# ----- Input Constraints -----
total_trip_days = 22

# Required cities with their durations (each duration includes full days counted; note flight days overlap)
city_durations = {
    "Istanbul": 5,    # Must attend annual show day1-5 → fixed as first city
    "Brussels": 3,
    "Milan": 4,
    "Split": 4,
    "Helsinki": 3,
    "Dubrovnik": 2,
    "Frankfurt": 3,   # Wedding must be attended between day16 and day18 within this stay.
    "Vilnius": 5      # Workshop in Vilnius must be attended between day18 and day22.
}

# ----- Flight Network -----
# Represent allowed direct flights as (origin, destination)
# Most flights are bidirectional except those specified as one-way.
allowed_flights = set()

# Helper function to add bidirectional edge
def add_bidirectional(a, b):
    allowed_flights.add((a, b))
    allowed_flights.add((b, a))

# Milan and Frankfurt
add_bidirectional("Milan", "Frankfurt")
# Split and Frankfurt
add_bidirectional("Split", "Frankfurt")
# Milan and Split
add_bidirectional("Milan", "Split")
# Brussels and Vilnius
add_bidirectional("Brussels", "Vilnius")
# Brussels and Helsinki
add_bidirectional("Brussels", "Helsinki")
# Istanbul and Brussels
add_bidirectional("Istanbul", "Brussels")
# Milan and Vilnius
add_bidirectional("Milan", "Vilnius")
# Brussels and Milan
add_bidirectional("Brussels", "Milan")
# Istanbul and Helsinki
add_bidirectional("Istanbul", "Helsinki")
# Helsinki and Vilnius
add_bidirectional("Helsinki", "Vilnius")
# Helsinki and Dubrovnik
add_bidirectional("Helsinki", "Dubrovnik")
# Split and Vilnius
add_bidirectional("Split", "Vilnius")
# from Dubrovnik to Istanbul (directional: only from Dubrovnik to Istanbul)
allowed_flights.add(("Dubrovnik", "Istanbul"))
# Istanbul and Milan
add_bidirectional("Istanbul", "Milan")
# Helsinki and Frankfurt
add_bidirectional("Helsinki", "Frankfurt")
# Istanbul and Vilnius
add_bidirectional("Istanbul", "Vilnius")
# Split and Helsinki
add_bidirectional("Split", "Helsinki")
# Milan and Helsinki
add_bidirectional("Milan", "Helsinki")
# Istanbul and Frankfurt
add_bidirectional("Istanbul", "Frankfurt")
# from Brussels to Frankfurt (directional: only from Brussels to Frankfurt)
allowed_flights.add(("Brussels", "Frankfurt"))
# Dubrovnik and Frankfurt
add_bidirectional("Dubrovnik", "Frankfurt")
# Frankfurt and Vilnius
add_bidirectional("Frankfurt", "Vilnius")

# ----- Functions to Check Itinerary Validity -----
# Given an ordering (list of cities), compute the schedule (start and finish day for each city)
def compute_schedule(order):
    schedule = []
    # First city always starts on day 1
    start_day = 1
    for city in order:
        duration = city_durations[city]
        finish_day = start_day + duration - 1
        schedule.append((city, start_day, finish_day))
        # Next city starts on the finish day (flight day overlaps)
        start_day = finish_day
    return schedule

# Check if the flight leg exists from city A to B in our allowed_flights
def flight_exists(city_a, city_b):
    return (city_a, city_b) in allowed_flights

# Check if a segment (start, finish) overlaps with a given event window [event_start, event_end]
def segment_overlaps(start, finish, event_start, event_end):
    # They overlap if the segment and event window share at least one day.
    return not (finish < event_start or start > event_end)

# Validate a complete itinerary order with its computed schedule
def is_valid_itinerary(order, schedule):
    # Constraint: Istanbul must be first (festival day 1-5).
    if order[0] != "Istanbul":
        return False
    # Check flight connectivity for each consecutive pair.
    for i in range(len(order) - 1):
        if not flight_exists(order[i], order[i+1]):
            return False
    # Check special event constraints:
    for city, start, finish in schedule:
        if city == "Istanbul":
            # Istanbul festival from day 1 to 5 must be attended.
            if start != 1 or finish < 5:
                return False
        if city == "Frankfurt":
            # Wedding between day 16 and 18: Frankfurt stay must include at least one day in [16,18]
            if not segment_overlaps(start, finish, 16, 18):
                return False
        if city == "Vilnius":
            # Workshop between day 18 and 22: Vilnius stay must include at least one day in [18,22]
            if not segment_overlaps(start, finish, 18, 22):
                return False
    # The overall trip days should equal total_trip_days. (This is automatically satisfied by the durations and overlaps.)
    # We'll check the finish day of the last city.
    if schedule[-1][2] != total_trip_days:
        return False
    return True

# ----- Search for a Valid Itinerary -----
def find_itinerary():
    all_cities = list(city_durations.keys())
    # We force Istanbul to be first.
    remaining_cities = [city for city in all_cities if city != "Istanbul"]
    # We'll try all permutations of the remaining cities.
    for perm in itertools.permutations(remaining_cities):
        order = ["Istanbul"] + list(perm)
        schedule = compute_schedule(order)
        if is_valid_itinerary(order, schedule):
            # Found a valid itinerary; return its schedule.
            return schedule
    return None

def main():
    schedule = find_itinerary()
    if schedule is None:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        for city, start, finish in schedule:
            day_range = f"Day {start}-{finish}"
            itinerary_list.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_list}
    # Output the result as JSON.
    print(json.dumps(result))

if __name__ == '__main__':
    main()