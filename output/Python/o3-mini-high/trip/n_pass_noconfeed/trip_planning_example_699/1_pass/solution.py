import itertools
import json

def compute_schedule(order, durations):
    schedule = []
    # The first city starts on day 1.
    start_day = 1
    for city in order:
        d = durations[city]
        # If you fly out on the last day of a city’s stay,
        # that day counts for both the current city and the next.
        end_day = start_day + d - 1
        schedule.append((city, start_day, end_day))
        # Next city is entered on the same day as the previous city's departure.
        start_day = end_day
    return schedule

def main():
    total_trip_days = 16

    # Define required durations for each city.
    durations = {
        "Hamburg": 2,    # Must meet friends between day 1 and day 2.
        "Dublin": 5,     # Also, the annual show in Dublin is from day 2 to day 6.
        "Helsinki": 4,
        "Reykjavik": 2,  # Wedding in Reykjavik must be attended between day 9 and day 10.
        "London": 5,
        "Mykonos": 3
    }
    
    # Direct flight connections (bidirectional).
    allowed_flights = [
        ("Dublin", "London"),
        ("Hamburg", "Dublin"),
        ("Helsinki", "Reykjavik"),
        ("Hamburg", "London"),
        ("Dublin", "Helsinki"),
        ("Reykjavik", "London"),
        ("London", "Mykonos"),
        ("Dublin", "Reykjavik"),
        ("Hamburg", "Helsinki"),
        ("Helsinki", "London")
    ]
    # Represent flights as a set of frozensets for easy lookup.
    flights = set(frozenset(pair) for pair in allowed_flights)
    
    # Fixed constraints: Must start at Hamburg (friends meeting between day 1-2)
    # and Dublin must be the second city (to attend the show from day 2-6).
    fixed_order = ["Hamburg", "Dublin"]
    # The remaining cities to order.
    remaining_cities = [city for city in durations if city not in fixed_order]
    
    valid_order = None
    valid_schedule = None
    
    # Try every permutation of the remaining cities.
    for perm in itertools.permutations(remaining_cities):
        order = fixed_order + list(perm)
        # Check if all consecutive cities are connected by a direct flight.
        connected = True
        for i in range(len(order) - 1):
            if frozenset((order[i], order[i+1])) not in flights:
                connected = False
                break
        if not connected:
            continue
        
        # Compute the day schedule.
        schedule = compute_schedule(order, durations)
        # Check that the last day of the itinerary equals the total trip days.
        if schedule[-1][2] != total_trip_days:
            continue
        
        # Verify Dublin's schedule: must cover day 2 to day 6.
        for city, start, end in schedule:
            if city == "Dublin":
                if start != 2 or end != 6:
                    connected = False
                break
        if not connected:
            continue

        # Verify the wedding in Reykjavik: you must be in Reykjavik on day 9 or day 10.
        # With a 2-day stay, ideally Reykjavik should span day 9 and day 10.
        for city, start, end in schedule:
            if city == "Reykjavik":
                if not (start <= 9 and end >= 10):
                    connected = False
                break
        if not connected:
            continue

        # Verify Hamburg: must be visited on day 1 and day 2.
        for city, start, end in schedule:
            if city == "Hamburg":
                if start != 1 or end != 2:
                    connected = False
                break
        if not connected:
            continue
        
        # If we've gotten here, the itinerary meets all constraints.
        valid_order = order
        valid_schedule = schedule
        break

    # Build the JSON output.
    if valid_schedule is None:
        output = {"itinerary": []}
    else:
        itinerary_list = []
        for city, start, end in valid_schedule:
            itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
        output = {"itinerary": itinerary_list}
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()