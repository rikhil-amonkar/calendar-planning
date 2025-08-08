#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the cities and their required durations
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    durations = {
        "Dublin": 5,
        "Helsinki": 3,
        "Riga": 3,
        "Reykjavik": 2,
        "Vienna": 2,
        "Tallinn": 5
    }
    
    # Define allowed direct flights.
    # For edges listed as "A and B" we add both (A,B) and (B,A).
    # For the flight "from Riga to Tallinn", we add only that direction.
    allowed_flights = {
        ("Helsinki", "Riga"), ("Riga", "Helsinki"),
        ("Riga", "Tallinn"),  # Only from Riga to Tallinn, not reverse.
        ("Vienna", "Helsinki"), ("Helsinki", "Vienna"),
        ("Riga", "Dublin"), ("Dublin", "Riga"),
        ("Vienna", "Riga"), ("Riga", "Vienna"),
        ("Reykjavik", "Vienna"), ("Vienna", "Reykjavik"),
        ("Helsinki", "Dublin"), ("Dublin", "Helsinki"),
        ("Tallinn", "Dublin"), ("Dublin", "Tallinn"),
        ("Reykjavik", "Helsinki"), ("Helsinki", "Reykjavik"),
        ("Reykjavik", "Dublin"), ("Dublin", "Reykjavik"),
        ("Helsinki", "Tallinn"), ("Tallinn", "Helsinki"),
        ("Vienna", "Dublin"), ("Dublin", "Vienna")
    }
    
    # Event constraints:
    # - In Vienna, attend annual show from day 2 to day 3.
    #   => Vienna's visit interval [start, end] must include both day 2 and day 3.
    # - In Helsinki, meet friends between day 3 and day 5.
    #   => Helsinki's visit interval must overlap with the range [3,5].
    # - In Tallinn, attend a wedding between day 7 and day 11.
    #   => Tallinn's visit interval must overlap with the range [7,11].
    
    valid_itinerary = None
    
    # Check all possible orders (permutations) of the six cities.
    for perm in itertools.permutations(cities):
        # Compute the timeline for the itinerary.
        # According to the rule, if you fly on day X from city A to city B,
        # then that day counts in both cities.
        # We set the start day for the first city as day 1.
        timeline = []  # Each element: (city, start_day, end_day)
        start_day = 1
        for city in perm:
            d = durations[city]
            end_day = start_day + d - 1
            timeline.append((city, start_day, end_day))
            # Next city starts on the same day as the current city's end (flight day overlap)
            start_day = end_day
            
        # Check that each flight between consecutive cities is allowed.
        valid_perm = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in allowed_flights:
                valid_perm = False
                break
        if not valid_perm:
            continue

        # Check event constraints based on the assigned day ranges.
        for city, s, e in timeline:
            if city == "Vienna":
                # Must cover day 2 to day 3.
                if not (s <= 2 and e >= 3):
                    valid_perm = False
                    break
            if city == "Helsinki":
                # Must overlap with days 3-5.
                if e < 3 or s > 5:
                    valid_perm = False
                    break
            if city == "Tallinn":
                # Must overlap with days 7-11.
                if e < 7 or s > 11:
                    valid_perm = False
                    break
        if not valid_perm:
            continue

        # If all constraints pass, we have found a valid itinerary.
        valid_itinerary = timeline
        break

    # Build the JSON result.
    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        for city, s, e in valid_itinerary:
            itinerary_list.append({"day_range": f"Day {s}-{e}", "place": city})
        result = {"itinerary": itinerary_list}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()