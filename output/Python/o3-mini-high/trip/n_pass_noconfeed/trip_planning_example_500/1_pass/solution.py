import json

def check_connectivity(route, flights):
    # Check that each consecutive leg in the route has a direct flight.
    for i in range(len(route) - 1):
        origin, dest = route[i], route[i+1]
        if ((origin, dest) not in flights) and ((dest, origin) not in flights):
            return False, (origin, dest)
    return True, None

def calculate_itinerary():
    # Trip constraints
    total_days = 20
    # Required durations in each city (the sum over cities is 7+7+2+6+2 = 24 days)
    # When a flight is taken on a day, that day counts for both the departure and arrival cities.
    city_durations = {
        "Hamburg": 7,
        "Split": 7,
        "Lyon": 2,       # Must cover the annual show on Day 13-14
        "Munich": 6,
        "Manchester": 2  # Must cover the relatives visit on Day 19-20
    }

    # Define direct flight connections (most flights are bidirectional,
    # except for the flight explicitly given "from Manchester to Split").
    flights = {
        ("Hamburg", "Munich"), ("Munich", "Hamburg"),
        ("Hamburg", "Manchester"), ("Manchester", "Hamburg"),
        ("Hamburg", "Split"), ("Split", "Hamburg"),
        ("Split", "Munich"), ("Munich", "Split"),
        ("Munich", "Manchester"), ("Manchester", "Munich"),
        ("Split", "Lyon"), ("Lyon", "Split"),
        ("Lyon", "Munich"), ("Munich", "Lyon"),
        ("Manchester", "Split")  # one directional flight as provided
    }

    # Choose an ordering of the cities that satisfies:
    # - The special event in Lyon (Day 13-14) -> Lyon must be in the itinerary such that its stay covers these days.
    # - The visit in Manchester (Day 19-20) -> Manchester must be the final destination.
    # - All legs must have direct flights.
    #
    # The following ordering satisfies:
    # Hamburg (7 days) -> Split (7 days) -> Lyon (2 days) -> Munich (6 days) -> Manchester (2 days)
    # Flight legs:
    #   Hamburg -> Split (direct)
    #   Split -> Lyon (direct)
    #   Lyon -> Munich (direct)
    #   Munich -> Manchester (direct)
    itinerary_order = ["Hamburg", "Split", "Lyon", "Munich", "Manchester"]

    valid, invalid_leg = check_connectivity(itinerary_order, flights)
    if not valid:
        raise ValueError(f"No direct flight available for leg: {invalid_leg}")

    # Compute itinerary segments.
    # Rule: If you fly from city A to city B on day X, then day X is counted in both cities.
    # So the end day of a city's stay is the same as the start day of the next city's stay.
    segments = []
    start_day = 1
    for city in itinerary_order:
        duration = city_durations[city]
        end_day = start_day + duration - 1  # The day of flight is counted in the stay.
        segments.append((city, start_day, end_day))
        # Next city's stay starts on the same day as the flight day (overlap).
        start_day = end_day

    # Verify that the final day matches the total trip duration.
    if segments[-1][2] != total_days:
        raise ValueError("The computed itinerary does not match the total trip duration.")

    # Verify special constraints.
    # For Lyon: must cover the annual show on Day 13-14.
    for city, s, e in segments:
        if city == "Lyon":
            if not (s <= 13 <= e and s <= 14 <= e):
                raise ValueError("Lyon's stay does not cover the show dates (Day 13-14).")

    # For Manchester: must cover the relatives visit on Day 19-20.
    for city, s, e in segments:
        if city == "Manchester":
            if not (s <= 19 <= e and s <= 20 <= e):
                raise ValueError("Manchester's stay does not cover the relatives visit dates (Day 19-20).")

    # Build the JSON itinerary.
    itinerary_list = []
    for city, s, e in segments:
        # Format the day range string.
        day_range = f"Day {s}-{e}"
        itinerary_list.append({"day_range": day_range, "place": city})

    return {"itinerary": itinerary_list}

def main():
    plan = calculate_itinerary()
    print(json.dumps(plan))

if __name__ == "__main__":
    main()