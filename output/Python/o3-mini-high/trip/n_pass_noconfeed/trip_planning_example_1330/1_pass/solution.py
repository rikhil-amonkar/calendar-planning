#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the cities with their required duration and, if applicable, an event window.
    # The event window is given as (event_start, event_end) and the constraint is that
    # the city's visitation period [start, end] must intersect with that window.
    cities = [
        {"name": "Salzburg", "duration": 2, "event": None},
        {"name": "Venice", "duration": 5, "event": None},
        {"name": "Bucharest", "duration": 4, "event": None},
        {"name": "Brussels", "duration": 2, "event": (21, 22)},       # meet friends between day 21-22
        {"name": "Hamburg", "duration": 4, "event": None},
        {"name": "Copenhagen", "duration": 4, "event": (18, 21)},     # wedding between day 18-21 (inclusive)
        {"name": "Nice", "duration": 3, "event": (9, 11)},            # relatives between day 9-11
        {"name": "Zurich", "duration": 5, "event": None},
        {"name": "Naples", "duration": 4, "event": (22, 25)}          # workshop between day 22-25
    ]

    # Define the available direct flights (undirected connections)
    flights_raw = [
        ("Zurich", "Brussels"),
        ("Bucharest", "Copenhagen"),
        ("Venice", "Brussels"),
        ("Nice", "Zurich"),
        ("Hamburg", "Nice"),
        ("Zurich", "Naples"),
        ("Hamburg", "Bucharest"),
        ("Zurich", "Copenhagen"),
        ("Bucharest", "Brussels"),
        ("Hamburg", "Brussels"),
        ("Venice", "Naples"),
        ("Venice", "Copenhagen"),
        ("Bucharest", "Naples"),
        ("Hamburg", "Copenhagen"),
        ("Venice", "Zurich"),
        ("Nice", "Brussels"),
        ("Hamburg", "Venice"),
        ("Copenhagen", "Naples"),
        ("Nice", "Naples"),
        ("Hamburg", "Zurich"),
        ("Salzburg", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Brussels", "Naples"),
        ("Copenhagen", "Brussels"),
        ("Venice", "Nice"),
        ("Nice", "Copenhagen")
    ]
    # Using frozensets makes the check undirected.
    flights = set(frozenset(pair) for pair in flights_raw)

    # Check that a given ordering (permutation) uses only available direct flights.
    def check_flight_connections(order):
        for i in range(len(order) - 1):
            city_a = order[i]["name"]
            city_b = order[i+1]["name"]
            if frozenset((city_a, city_b)) not in flights:
                return False
        return True

    # Given an ordering, compute the start and end day for each city.
    # The rule is: the first city starts on Day 1. When flying from city A to city B,
    # the flight day is the same day: if A is visited on [S, S+d_A-1], then city B starts on S+d_A-1.
    # Also check if the city's period [start, end] meets its event constraint (if any).
    def compute_itinerary(order):
        itinerary = []
        current_day = 1
        for city in order:
            start = current_day
            end = start + city["duration"] - 1
            # If there is an event, check that the visit interval [start, end] overlaps the event window.
            if city["event"]:
                event_start, event_end = city["event"]
                # The city's interval must have at least one day in the event window.
                if end < event_start or start > event_end:
                    return None
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city["name"]})
            # Set the next city's start as the same day as the current city's end (flight day overlap)
            current_day = end
        # The overall trip must finish on day 25.
        last_range = itinerary[-1]["day_range"]
        # Extract the ending day from the string "Day X-Y"
        try:
            end_day = int(last_range.split('-')[1])
        except (IndexError, ValueError):
            return None
        if end_day != 25:
            return None
        return itinerary

    # Iterate over all permutations to find one valid itinerary.
    for perm in itertools.permutations(cities):
        if not check_flight_connections(perm):
            continue
        itinerary = compute_itinerary(perm)
        if itinerary is None:
            continue
        # A valid itinerary has been found; output it as JSON.
        output = {"itinerary": itinerary}
        print(json.dumps(output))
        return

if __name__ == "__main__":
    main()