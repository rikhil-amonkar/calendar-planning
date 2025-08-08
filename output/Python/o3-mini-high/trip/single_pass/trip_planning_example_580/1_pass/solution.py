#!/usr/bin/env python3
import json
import itertools

def main():
    # Input parameters (constraints)
    total_trip_days = 23
    # Required days to spend per city
    durations = {
        "Paris": 6,
        "Oslo": 5,
        "Porto": 7,
        "Geneva": 7,
        "Reykjavik": 2
    }
    # Conference in Geneva on day 1 and day 7.
    # (We ensure these days fall in Geneva's segment.)
    conference_days = [1, 7]
    conference_city = "Geneva"
    
    # Must visit relatives in Oslo between these days (inclusive)
    relatives_oslo_window = (19, 23)  # (start, end)

    # List of cities to visit, exactly 5 distinct cities.
    cities = ["Geneva", "Paris", "Oslo", "Porto", "Reykjavik"]

    # Allowed direct flights (treat as undirected)
    allowed_flights_list = [
        ("Paris", "Oslo"),
        ("Geneva", "Oslo"),
        ("Porto", "Paris"),
        ("Geneva", "Paris"),
        ("Geneva", "Porto"),
        ("Paris", "Reykjavik"),
        ("Reykjavik", "Oslo"),
        ("Porto", "Oslo")
    ]
    # Build a set of frozensets for bidirectional lookup
    allowed_flights = set()
    for a, b in allowed_flights_list:
        allowed_flights.add(frozenset([a, b]))

    # Helper function to check direct flight connectivity between two cities
    def direct_flight_exists(city_a, city_b):
        return frozenset([city_a, city_b]) in allowed_flights

    # We want conference on day 1 and day 7 in Geneva.
    # To ensure day 1 is Geneva, we force Geneva as the first visited city.
    fixed_city = "Geneva"
    remaining_cities = [c for c in cities if c != fixed_city]

    valid_itinerary = None
    itinerary_segments = None

    # Generate candidate orders with Geneva fixed at the start
    for perm in itertools.permutations(remaining_cities):
        candidate = [fixed_city] + list(perm)
        # Check flight connectivity between consecutive cities
        valid = True
        for i in range(len(candidate)-1):
            if not direct_flight_exists(candidate[i], candidate[i+1]):
                valid = False
                break
        if not valid:
            continue

        # Simulate the timeline.
        # Rule: if you fly from city A to city B on day X,
        # then day X counts for both city A and city B.
        # So for the first city, start day = 1 and end = start + duration - 1.
        # For each subsequent city, start day equals the previous city's end day.
        timeline = []
        current_day = 1
        for city in candidate:
            start_day = current_day
            end_day = start_day + durations[city] - 1
            timeline.append((city, start_day, end_day))
            current_day = end_day  # Overlap: flight day is the same as end_day
        
        # Final day should equal total_trip_days.
        if current_day != total_trip_days:
            continue

        # Check conference constraint.
        # Conference must be held in Geneva on day 1 and day 7.
        # Find the segment where city is Geneva.
        geneva_valid = False
        for city, start_day, end_day in timeline:
            if city == conference_city:
                if start_day <= conference_days[0] and end_day >= conference_days[0] and \
                   start_day <= conference_days[1] and end_day >= conference_days[1]:
                    geneva_valid = True
                    break
        if not geneva_valid:
            continue

        # Check relative meeting in Oslo between day 19 and day 23.
        oslo_valid = False
        for city, start_day, end_day in timeline:
            if city == "Oslo":
                # Check if there is any overlap with [19, 23]
                if end_day >= relatives_oslo_window[0] and start_day <= relatives_oslo_window[1]:
                    oslo_valid = True
                    break
        if not oslo_valid:
            continue

        # If all constraints are met, build the itinerary segments output.
        segments_output = []
        for city, start_day, end_day in timeline:
            segments_output.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
        valid_itinerary = candidate
        itinerary_segments = segments_output
        break

    # If no valid itinerary is found, output an empty itinerary.
    result = {"itinerary": itinerary_segments if itinerary_segments is not None else []}
    print(json.dumps(result))

if __name__ == "__main__":
    main()