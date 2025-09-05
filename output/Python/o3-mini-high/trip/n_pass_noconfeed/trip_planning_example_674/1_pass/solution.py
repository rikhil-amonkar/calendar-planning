#!/usr/bin/env python3
import itertools
import json

# Function to check if a direct flight exists from city_from to city_to.
def flight_exists(city_from, city_to, bidir, directionals):
    # If there is a bidirectional connection, it works both ways.
    if frozenset([city_from, city_to]) in bidir:
        return True
    # Check if there is a directional connection (only allowed in the specified direction).
    if (city_from, city_to) in directionals:
        return True
    return False

# Compute the timeline for an itinerary given the overlapping flight concept.
# The first city starts on day 1. When flying from one city to the next on the last day
# of the current segment, that day counts for both.
def compute_timeline(order, durations):
    start_days = []
    end_days = []
    current_day = 1
    for city in order:
        start_days.append(current_day)
        # The segment for a city lasts for its full duration.
        end_day = current_day + durations[city] - 1
        end_days.append(end_day)
        # Next city’s segment starts on the same day of flight (overlap)
        current_day = end_day
    return start_days, end_days

# Validate the itinerary timeline against the overall day limit and specific time constraints.
def itinerary_valid(order, durations, total_days):
    start_days, end_days = compute_timeline(order, durations)
    # The final day must equal the total trip days.
    if end_days[-1] != total_days:
        return False, None, None
    # Helsinki must be visited first (to attend the workshop between day 1 and day 2).
    if order[0] != "Helsinki":
        return False, None, None
    # For Reykjavik, the friend must be met between day 8 and day 9.
    # This means the Reykjavik visit interval must overlap the window [8, 9].
    for i, city in enumerate(order):
        if city == "Reykjavik":
            if end_days[i] < 8 or start_days[i] > 9:
                return False, None, None
    # For Warsaw, the visit to relatives must be between day 9 and day 11.
    for i, city in enumerate(order):
        if city == "Warsaw":
            if end_days[i] < 9 or start_days[i] > 11:
                return False, None, None
    return True, start_days, end_days

# Try to compute a valid itinerary (order of cities) that satisfies all flight connections and time constraints.
def compute_itinerary(cities, durations, total_days, bidir, directionals):
    # Helsinki must be the first city.
    remaining = [c for c in cities if c != "Helsinki"]
    for perm in itertools.permutations(remaining):
        order = ["Helsinki"] + list(perm)
        valid_flights = True
        # Check that each consecutive pair has a direct flight.
        for i in range(len(order) - 1):
            if not flight_exists(order[i], order[i+1], bidir, directionals):
                valid_flights = False
                break
        if not valid_flights:
            continue
        valid, start_days, end_days = itinerary_valid(order, durations, total_days)
        if valid:
            return order, start_days, end_days
    return None, None, None

def main():
    # Total trip duration
    total_days = 14

    # List of 6 European cities.
    cities = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]

    # Required durations (in days) to be spent in each city.
    durations = {
        "Helsinki": 2,   # Workshop between day 1 and 2 must occur here.
        "Warsaw": 3,     # Relatives visit between day 9 and 11.
        "Madrid": 4,
        "Split": 4,
        "Reykjavik": 2,  # Meet friend between day 8 and 9.
        "Budapest": 4
    }

    # Define the flight connectivity.
    # These flights (except the directional one) are bidirectional.
    bidirectional_flights = {
        frozenset(["Helsinki", "Reykjavik"]),
        frozenset(["Budapest", "Warsaw"]),
        frozenset(["Madrid", "Split"]),
        frozenset(["Helsinki", "Split"]),
        frozenset(["Helsinki", "Madrid"]),
        frozenset(["Helsinki", "Budapest"]),
        frozenset(["Reykjavik", "Warsaw"]),
        frozenset(["Helsinki", "Warsaw"]),
        frozenset(["Madrid", "Budapest"]),
        frozenset(["Budapest", "Reykjavik"]),
        frozenset(["Madrid", "Warsaw"]),
        frozenset(["Warsaw", "Split"])
    }
    # There is one directional flight (only from Reykjavik to Madrid is allowed).
    directional_flights = {("Reykjavik", "Madrid")}

    order, start_days, end_days = compute_itinerary(cities, durations, total_days, bidirectional_flights, directional_flights)

    if order is None:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        for city, start, end in zip(order, start_days, end_days):
            itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
        result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()