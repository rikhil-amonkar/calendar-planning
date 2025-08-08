#!/usr/bin/env python3
import itertools
import json

def main():
    # Total trip days
    total_days = 22

    # Cities and required durations (in days)
    cities = ["Valencia", "Riga", "Prague", "Mykonos", "Zurich", "Bucharest", "Nice"]
    durations = {
        "Valencia": 5,
        "Riga": 5,
        "Prague": 3,
        "Mykonos": 3,
        "Zurich": 5,
        "Bucharest": 5,
        "Nice": 2
    }

    # Flight connections (undirected edges)
    flight_edges = [
        ("Mykonos", "Nice"),
        ("Mykonos", "Zurich"),
        ("Prague", "Bucharest"),
        ("Valencia", "Bucharest"),
        ("Zurich", "Prague"),
        ("Riga", "Nice"),
        ("Zurich", "Riga"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Valencia"),
        ("Bucharest", "Riga"),
        ("Prague", "Riga"),
        ("Prague", "Valencia"),
        ("Zurich", "Nice")
    ]
    # Build a set of undirected connections for easy lookup.
    flights_set = set(frozenset((a, b)) for a, b in flight_edges)

    # Constraint functions:
    # For Mykonos: attend wedding between day1 and day3.
    # Our itinerary is built so that the first city starts on day 1 and subsequent cities start on a later day.
    # For Mykonos, because its duration is 3 days (range: start to start+2),
    # we require that its start day is <= 3 to ensure one of its days falls in [1,3].
    def wedding_constraint(start_day, city):
        if city == "Mykonos":
            return start_day <= 3
        return True

    # For Prague: visit relatives between day 7 and day 9.
    # Prague’s 3-day range is [start, start+2]. We require there be overlap with [7,9].
    # This is true if start_day <= 9 and start_day+2 >= 7.
    def relatives_constraint(start_day, city):
        if city == "Prague":
            return (start_day <= 9) and (start_day + 2 >= 7)
        return True

    # Given an ordering, compute the start day for each city.
    # The rules: The first city begins on day 1 and occupies days [1, d1].
    # When flying on the final day of a city, that same day counts as the arrival day for the next city.
    # Therefore, the start day for city i (i>=1) is: start_day[i] = start_day[i-1] + (duration(previous) - 1).
    def compute_start_days(order):
        start_days = []
        current = 1
        for city in order:
            start_days.append(current)
            current = current + durations[city] - 1
        return start_days

    valid_itinerary = None

    # Iterate over all permutations of the cities.
    for order in itertools.permutations(cities):
        # Check flight connectivity for every consecutive pair.
        route_valid = True
        for i in range(len(order) - 1):
            if frozenset((order[i], order[i+1])) not in flights_set:
                route_valid = False
                break
        if not route_valid:
            continue

        # Compute the start days for each city in this order.
        start_days = compute_start_days(order)

        # Check event constraints for each city in the itinerary.
        meets_constraints = True
        for idx, city in enumerate(order):
            s_day = start_days[idx]
            if not wedding_constraint(s_day, city):
                meets_constraints = False
                break
            if not relatives_constraint(s_day, city):
                meets_constraints = False
                break
        if not meets_constraints:
            continue

        # Check that the itinerary exactly fills the total trip days.
        # The last city's end day is start_day + (duration - 1).
        if start_days[-1] + durations[order[-1]] - 1 != total_days:
            continue

        # If we reach here, we have found a valid itinerary.
        itinerary = []
        for idx, city in enumerate(order):
            start = start_days[idx]
            end = start + durations[city] - 1
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
        valid_itinerary = itinerary
        break

    if valid_itinerary is None:
        result = {"itinerary": "No valid itinerary found"}
    else:
        result = {"itinerary": valid_itinerary}

    # Output the result as JSON.
    print(json.dumps(result))

if __name__ == "__main__":
    main()