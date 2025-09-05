import itertools
import json

def main():
    # Trip constraints
    total_trip_days = 12
    cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
    # Required days to be spent in each city
    durations = {
        "Split": 2,
        "Helsinki": 2,
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6
    }
    
    # Special scheduling constraints:
    # You plan to visit relatives in Vilnius between day 7 and day 9.
    # That means the Vilnius leg (3 days) must exactly occur on days 7-9.
    vilnius_required_start = 7  # then it will run 7,8,9
    
    # You are attending a wedding in Reykjavik between day 10 and day 12.
    # The Reykjavik leg (3 days) must cover that window, so we require it to start on day 10.
    reykjavik_required_start = 10  # then it will run 10,11,12

    # Allowed direct flights (bidirectional)
    allowed_flights = {
        frozenset(["Split", "Helsinki"]),
        frozenset(["Geneva", "Split"]),
        frozenset(["Geneva", "Helsinki"]),
        frozenset(["Helsinki", "Reykjavik"]),
        frozenset(["Vilnius", "Helsinki"]),
        frozenset(["Split", "Vilnius"]),
    }

    # The itinerary’s total individual city-days is sum(durations) = 16.
    # With 4 transfers (overlap days), the actual trip duration is 16 - 4 = 12 days.
    
    # We try each permutation of the cities to find one that:
    # 1. Uses only direct flights for consecutive cities.
    # 2. Has the correct overall trip length (accounting for overlap).
    # 3. Satisfies the special timeline constraints for Vilnius and Reykjavik.
    optimal_itinerary = None

    # Permute the list to get an ordering of visits.
    for perm in itertools.permutations(cities):
        valid = True
        # Check direct flight connectivity for each consecutive pair.
        for i in range(len(perm) - 1):
            if frozenset([perm[i], perm[i+1]]) not in allowed_flights:
                valid = False
                break
        if not valid:
            continue

        # Compute the start day for each city segment.
        # When flying on day X from A to B, day X counts for both A and B.
        start_days = []
        current_day = 1
        for city in perm:
            start_days.append(current_day)
            # After spending the required days in a city, we fly on the last day's end.
            # So the next city starts on the same day that the previous city ended.
            current_day = current_day + durations[city] - 1

        # The final day in the itinerary is the last city's start day plus its duration minus 1.
        final_day = start_days[-1] + durations[perm[-1]] - 1
        if final_day != total_trip_days:
            continue

        # Check special constraints for Vilnius.
        try:
            vilnius_index = perm.index("Vilnius")
        except ValueError:
            continue
        if start_days[vilnius_index] != vilnius_required_start:
            continue

        # Check special constraints for Reykjavik.
        try:
            reykjavik_index = perm.index("Reykjavik")
        except ValueError:
            continue
        if start_days[reykjavik_index] != reykjavik_required_start:
            continue

        # If all conditions are met, compute the itinerary with day ranges.
        itinerary_list = []
        for i, city in enumerate(perm):
            start = start_days[i]
            end = start + durations[city] - 1
            itinerary_list.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
        optimal_itinerary = {"itinerary": itinerary_list}
        break

    if optimal_itinerary is None:
        # No valid itinerary found that meets all constraints.
        optimal_itinerary = {"itinerary": []}

    print(json.dumps(optimal_itinerary))

if __name__ == "__main__":
    main()