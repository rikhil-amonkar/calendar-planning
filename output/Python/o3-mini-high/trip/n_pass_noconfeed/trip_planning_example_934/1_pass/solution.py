import itertools
import json

# Trip constraints
total_trip_days = 17

# Durations for each city (the “allocated” days in that city, recall flight days are double counted)
city_durations = {
    "Brussels": 5,
    "Rome": 2,
    "Dubrovnik": 3,
    "Geneva": 5,
    "Budapest": 2,
    "Riga": 4,
    "Valencia": 2
}

# Event constraints are given as (min_day, max_day) that an event must occur within the city's stay.
# For Brussels, workshop between day 7 and 11.
# For Riga, friend meeting between day 4 and 7.
# For Budapest, friend meeting between day 16 and 17.
event_constraints = {
    "Brussels": (7, 11),
    "Riga": (4, 7),
    "Budapest": (16, 17)
}

# Allowed direct flights.
# For bidirectional flights, we add both directions.
# Note: "from Rome to Riga" is only allowed in that direction.
allowed_flights = set()

def add_bidirectional(a, b):
    allowed_flights.add((a, b))
    allowed_flights.add((b, a))

# Brussels and Valencia (bidirectional)
add_bidirectional("Brussels", "Valencia")
# Rome and Valencia
add_bidirectional("Rome", "Valencia")
# Brussels and Geneva
add_bidirectional("Brussels", "Geneva")
# Rome and Geneva
add_bidirectional("Rome", "Geneva")
# Dubrovnik and Geneva
add_bidirectional("Dubrovnik", "Geneva")
# Valencia and Geneva
add_bidirectional("Valencia", "Geneva")
# from Rome to Riga (only one direction)
allowed_flights.add(("Rome", "Riga"))
# Geneva and Budapest
add_bidirectional("Geneva", "Budapest")
# Riga and Brussels
add_bidirectional("Riga", "Brussels")
# Rome and Budapest
add_bidirectional("Rome", "Budapest")
# Rome and Brussels
add_bidirectional("Rome", "Brussels")
# Brussels and Budapest
add_bidirectional("Brussels", "Budapest")
# Dubrovnik and Rome
add_bidirectional("Dubrovnik", "Rome")

cities = list(city_durations.keys())

def compute_itinerary(order):
    """
    Given an order of cities (list of strings), compute the day range for each city.
    Flight rule: if you fly on day X from city A to B, then city A and city B both count day X.
    Thus, for the first city, start_day = 1, end_day = duration.
    For each subsequent city, start_day = previous end_day, end_day = start_day + duration - 1.
    Returns a list of tuples (city, start, end).
    """
    itinerary = []
    current_day = 1
    for city in order:
        duration = city_durations[city]
        start = current_day
        end = start + duration - 1
        itinerary.append((city, start, end))
        # Next city's start is the same as the current flight (current day counted twice)
        current_day = end
    return itinerary

def satisfies_event(city, start, end):
    """
    Check if the interval [start, end] (inclusive) for the city meets its event constraint.
    That is, the intersection with the event window must be non-empty.
    If there is no event constraint for the city, return True.
    """
    if city not in event_constraints:
        return True
    ev_min, ev_max = event_constraints[city]
    # Intersection condition: not (end < ev_min or start > ev_max)
    return not (end < ev_min or start > ev_max)

def is_valid_flight_path(order):
    """
    Check that for each consecutive pair in the given order, there is an allowed direct flight.
    """
    for i in range(len(order) - 1):
        if (order[i], order[i+1]) not in allowed_flights:
            return False
    return True

def main():
    valid_itinerary = None

    # Enumerate all permutations of the 7 cities
    for perm in itertools.permutations(cities):
        # Check direct flight connectivity between consecutive cities
        if not is_valid_flight_path(perm):
            continue

        # Compute the day intervals (taking into account flight day overlaps)
        itinerary_schedule = compute_itinerary(perm)
        # Total trip days should equal total_trip_days
        if itinerary_schedule[-1][2] != total_trip_days:
            continue

        # Check event constraints for cities that have them
        event_ok = True
        for city, start, end in itinerary_schedule:
            if not satisfies_event(city, start, end):
                event_ok = False
                break
        if not event_ok:
            continue

        # Found a valid itinerary!
        valid_itinerary = itinerary_schedule
        break

    if valid_itinerary is None:
        output = {"itinerary": []}
    else:
        # Build JSON output: list of dictionaries with day_range and place.
        itinerary_list = []
        for city, start, end in valid_itinerary:
            day_range = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range, "place": city})
        output = {"itinerary": itinerary_list}
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()