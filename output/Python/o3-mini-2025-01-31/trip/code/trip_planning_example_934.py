import json

def compute_itinerary():
    # Input parameters:
    total_days = 17

    # Desired cities and their intended durations (in days)
    # Note: When flying, the flight day is shared between the departure city and arrival city.
    durations = {
        "Brussels": 5,   # Must include a workshop between day 7-11.
        "Rome": 2,
        "Dubrovnik": 3,
        "Geneva": 5,
        "Budapest": 2,   # Must meet friend in Budapest between day 16-17.
        "Riga": 4,      # Must meet friends in Riga between day 4-7.
        "Valencia": 2
    }
    
    # Allowed direct flights (bidirectional unless noted otherwise)
    # Represented as sets of frozensets (or tuples for one-way flights)
    flights = {
        frozenset(["Brussels", "Valencia"]),
        frozenset(["Rome", "Valencia"]),
        frozenset(["Brussels", "Geneva"]),
        frozenset(["Rome", "Geneva"]),
        frozenset(["Dubrovnik", "Geneva"]),
        frozenset(["Valencia", "Geneva"]),
        # For the special flight from Rome to Riga, we denote it as one-way.
        ("Rome", "Riga"),
        frozenset(["Geneva", "Budapest"]),
        frozenset(["Riga", "Brussels"]),
        frozenset(["Rome", "Budapest"]),
        frozenset(["Rome", "Brussels"]),
        frozenset(["Brussels", "Budapest"]),
        frozenset(["Dubrovnik", "Rome"])
    }
    
    # We choose the itinerary order that can meet all constraints and flight connections.
    # Sequence chosen: Riga -> Brussels -> Valencia -> Rome -> Dubrovnik -> Geneva -> Budapest
    # Check flight connectivity:
    # Riga -> Brussels: allowed (Riga and Brussels are connected).
    # Brussels -> Valencia: allowed.
    # Valencia -> Rome: allowed.
    # Rome -> Dubrovnik: allowed.
    # Dubrovnik -> Geneva: allowed.
    # Geneva -> Budapest: allowed.
    sequence = ["Riga", "Brussels", "Valencia", "Rome", "Dubrovnik", "Geneva", "Budapest"]
    
    # Check that every consecutive flight is allowed.
    def is_flight_allowed(city_from, city_to):
        # First, check one-way flight from city_from to city_to
        if (city_from, city_to) in flights:
            return True
        # Then, check bidirectional flights (if the frozenset is in flights)
        if frozenset([city_from, city_to]) in flights:
            return True
        return False

    for i in range(len(sequence) - 1):
        if not is_flight_allowed(sequence[i], sequence[i+1]):
            raise ValueError(f"No direct flight available from {sequence[i]} to {sequence[i+1]}.")

    # Calculate day ranges.
    # Because each transition (flight day) is counted in both the departure and arrival city,
    # the effective new days added for each city after the first is (duration - 1).
    itinerary = []
    current_day = 1
    for idx, city in enumerate(sequence):
        duration = durations[city]
        if idx == 0:
            # First city: no overlap at start.
            start_day = current_day
            end_day = start_day + duration - 1
            itinerary.append({"day_range": f"{start_day}-{end_day}", "place": city})
            current_day = end_day  # Next flight day overlaps.
        else:
            # For subsequent cities, the flight day counts in both the previous and the current city.
            start_day = current_day  # Overlap day from previous segment.
            # This city contributes (duration - 1) additional days after the overlap.
            end_day = start_day + duration - 1
            itinerary.append({"day_range": f"{start_day}-{end_day}", "place": city})
            current_day = end_day

    # Validate overall day count.
    if current_day != total_days:
        raise ValueError(f"The computed itinerary does not exactly fill {total_days} days. Total computed days: {current_day}")

    return itinerary

if __name__ == "__main__":
    itinerary_plan = compute_itinerary()
    print(json.dumps(itinerary_plan))