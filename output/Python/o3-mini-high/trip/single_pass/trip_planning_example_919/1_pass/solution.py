#!/usr/bin/env python3
import itertools
import json

def main():
    total_days = 15

    # Define the required durations for each city
    city_durations = {
        "Vienna": 4,
        "Milan": 2,
        "Rome": 3,
        "Riga": 2,
        "Lisbon": 3,
        "Vilnius": 4,
        "Oslo": 3
    }

    # Special constraints: conference in Vienna (must be on day 1 and day 4),
    # Lisbon visit (must cover at least one day between day 11 and 13),
    # and Oslo visit (must cover at least one day between day 13 and 15)
    vienna_conference_days = {1, 4}
    lisbon_relatives_days = {11, 12, 13}
    oslo_friend_days = {13, 14, 15}

    # Setup allowed direct flights.
    # For bidirectional flights, we add both (A,B) and (B,A).
    allowed_flights = set()

    def add_bidirectional(a, b):
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))

    def add_directional(a, b):
        allowed_flights.add((a, b))

    add_bidirectional("Riga", "Oslo")
    add_bidirectional("Rome", "Oslo")
    add_bidirectional("Vienna", "Milan")
    add_bidirectional("Vienna", "Vilnius")
    add_bidirectional("Vienna", "Lisbon")
    add_bidirectional("Riga", "Milan")
    add_bidirectional("Lisbon", "Oslo")
    add_directional("Rome", "Riga")
    add_bidirectional("Rome", "Lisbon")
    add_bidirectional("Vienna", "Riga")
    add_bidirectional("Vienna", "Rome")
    add_bidirectional("Milan", "Oslo")
    add_bidirectional("Vienna", "Oslo")
    add_bidirectional("Vilnius", "Oslo")
    add_directional("Riga", "Vilnius")
    add_bidirectional("Vilnius", "Milan")
    add_bidirectional("Riga", "Lisbon")
    add_bidirectional("Milan", "Lisbon")

    # Fixed start and end cities.
    start_city = "Vienna"
    end_city = "Oslo"

    # All cities must be visited.
    all_cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    # Intermediate cities (excluding the fixed start and end)
    intermediate_cities = [city for city in all_cities if city not in (start_city, end_city)]

    valid_itinerary = None

    # Try every permutation of the intermediate cities.
    for perm in itertools.permutations(intermediate_cities):
        # Construct full order with the fixed start and end.
        itinerary_order = [start_city] + list(perm) + [end_city]

        # Check that each consecutive pair is connected by a direct flight.
        valid_route = True
        for i in range(len(itinerary_order) - 1):
            if (itinerary_order[i], itinerary_order[i+1]) not in allowed_flights:
                valid_route = False
                break
        if not valid_route:
            continue

        # Calculate the day intervals for each city.
        # On the first city, start day is 1.
        # For each subsequent city, the start day is equal to
        # the previous city's end day (flight day counts for both cities).
        current_day = 1
        itinerary_segments = []  # Will store tuples: (city, start_day, end_day)
        for city in itinerary_order:
            start = current_day
            end = start + city_durations[city] - 1
            itinerary_segments.append((city, start, end))
            current_day = end  # Overlap: flight day is the same as the previous end day

        # Check if the itinerary exactly spans the total_days.
        if itinerary_segments[-1][2] != total_days:
            continue

        # Verify special constraints.
        valid_special = True
        for city, start, end in itinerary_segments:
            days_in_city = set(range(start, end + 1))
            if city == "Vienna":
                if not vienna_conference_days.issubset(days_in_city):
                    valid_special = False
                    break
            if city == "Lisbon":
                if days_in_city.isdisjoint(lisbon_relatives_days):
                    valid_special = False
                    break
            if city == "Oslo":
                if days_in_city.isdisjoint(oslo_friend_days):
                    valid_special = False
                    break
        if not valid_special:
            continue

        # Found a valid itinerary.
        valid_itinerary = itinerary_segments
        break

    # Prepare the output in the required JSON format.
    output = {"itinerary": []}
    if valid_itinerary:
        for city, start, end in valid_itinerary:
            output["itinerary"].append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })

    print(json.dumps(output))

if __name__ == "__main__":
    main()