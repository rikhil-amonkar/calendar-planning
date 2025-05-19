import json

def main():
    # Input constraints
    total_days = 18
    # Cities with required stays (including flight overlap)
    # Each value is the total required stay count when counted with flight overlap.
    required_stays = {
        "Venice": 5,     # Also must be present from day 1 to day 5 for the show.
        "Stuttgart": 3,
        "Stockholm": 2,
        "Barcelona": 2,
        "Florence": 4,
        "Frankfurt": 4,
        "Salzburg": 4
    }
    
    # Direct flight connections available (bidirectional assumed)
    # Represented as a set of frozensets.
    direct_flights = {
        frozenset(["Barcelona", "Frankfurt"]),
        frozenset(["Florence", "Frankfurt"]),
        frozenset(["Stockholm", "Barcelona"]),
        frozenset(["Barcelona", "Florence"]),
        frozenset(["Venice", "Barcelona"]),
        frozenset(["Stuttgart", "Barcelona"]),
        frozenset(["Frankfurt", "Salzburg"]),
        frozenset(["Stockholm", "Frankfurt"]),
        frozenset(["Stuttgart", "Stockholm"]),
        frozenset(["Stuttgart", "Frankfurt"]),
        frozenset(["Venice", "Stuttgart"]),
        frozenset(["Venice", "Frankfurt"]),
    }
    
    # We choose an ordering that satisfies:
    # - The show in Venice from day 1 to day 5 (so Venice is first)
    # - Only use direct flights between consecutive cities.
    # - The overlapping flight days reduce total sum days to total_days.
    #
    # The chosen ordering is:
    # 1. Venice (5 days) - days 1 to 5. (The annual show is here days 1-5.)
    # 2. Stuttgart (3 days) - flight day overlap on day 5, then days 6 and 7.
    # 3. Stockholm (2 days) - flight day overlap on day 7, then day 8.
    # 4. Barcelona (2 days) - flight day overlap on day 8, then day 9.
    # 5. Florence (4 days) - flight day overlap on day 9, then days 10, 11, 12.
    # 6. Frankfurt (4 days) - flight day overlap on day 12, then days 13, 14, 15.
    # 7. Salzburg (4 days) - flight day overlap on day 15, then days 16, 17, 18.
    #
    # Verify connectivity between consecutive cities using direct flights.
    itinerary_order = ["Venice", "Stuttgart", "Stockholm", "Barcelona", "Florence", "Frankfurt", "Salzburg"]
    
    # Check flight connectivity in the chosen itinerary order:
    for i in range(len(itinerary_order) - 1):
        cityA = itinerary_order[i]
        cityB = itinerary_order[i + 1]
        if frozenset([cityA, cityB]) not in direct_flights:
            raise ValueError(f"No direct flight between {cityA} and {cityB}")
    
    # Calculate the day ranges:
    itinerary = []
    current_day = 1
    for idx, city in enumerate(itinerary_order):
        stay = required_stays[city]
        # For every flight connection, the flight day is the last day of the previous city and the first day of the next city.
        # Thus, each new city (except the first) starts on the same day the flight happens.
        # Therefore, schedule as:
        # - First city: day current_day to (current_day + stay - 1)
        # - Next city: flight day is the first day for the new city, equals previous city's end day.
        start_day = current_day
        end_day = start_day + stay - 1
        # For next segment, the flight will occur on end_day.
        # So the next city will start on end_day (overlap).
        itinerary.append({
            "day_range": f"{start_day}-{end_day}",
            "place": city
        })
        # Set next start day: if this is not the last city, the flight day (end_day) is counted for the next city.
        current_day = end_day
        if idx < len(itinerary_order) - 1:
            # Move to the day after the flight day – however, because flight day counts for both cities,
            # the next city effectively starts on the same day as the flight day.
            # So we do not add 1 here; current_day remains as the overlapping flight day.
            pass

    # current_day now is the last day of arrival in the final city. It should equal total_days.
    # Validate overall schedule:
    if current_day != total_days:
        raise ValueError("The computed itinerary does not add up to the total days required.")

    # Output the result in JSON format (list of dictionaries with day_range and place)
    print(json.dumps(itinerary, indent=4))

if __name__ == "__main__":
    main()