import itertools
import json

def main():
    # Total unique days of the trip
    total_days = 18

    # Trip constraints: required days (including flight overlap days) for each city.
    durations = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4
    }
    
    # Direct flight connections (bidirectional).
    flights = {
        "Helsinki": ["Prague", "Reykjavik", "Dubrovnik"],
        "Prague": ["Helsinki", "Valencia", "Reykjavik"],
        "Valencia": ["Prague", "Porto"],
        "Porto": ["Valencia"],
        "Reykjavik": ["Helsinki", "Prague"],
        "Dubrovnik": ["Helsinki"]
    }
    
    # List of cities to visit (6 cities)
    cities = list(durations.keys())
    
    valid_itinerary = None

    # Try every permutation of cities and check if consecutive cities have direct flights.
    for perm in itertools.permutations(cities):
        valid_route = True
        for i in range(len(perm) - 1):
            current, next_city = perm[i], perm[i+1]
            # Check if a direct flight exists between current and next_city
            if next_city not in flights.get(current, []):
                valid_route = False
                break
        if not valid_route:
            continue

        # Compute the itinerary day ranges.
        # The rule: if you fly from A to B on day X, then day X counts for both A and B.
        itinerary = []
        current_day = 1
        porto_day_range = None
        for city in perm:
            start_day = current_day
            end_day = start_day + durations[city] - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
            if city == "Porto":
                porto_day_range = (start_day, end_day)
            # Next city starts on the same day as the end_day (flight day overlap)
            current_day = end_day

        # Ensure the trip spans exactly the total number of days.
        if current_day != total_days:
            continue

        # Check friend meeting constraint: meet in Porto between day 16 and day 18.
        if porto_day_range:
            p_start, p_end = porto_day_range
            # The Porto segment must include at least one day between 16 and 18.
            if p_end >= 16 and p_start <= 18:
                valid_itinerary = itinerary
                break

    # If a valid itinerary is found, output it as JSON.
    output = {"itinerary": valid_itinerary if valid_itinerary is not None else []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()