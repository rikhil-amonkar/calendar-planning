#!/usr/bin/env python3
import itertools
import json

def main():
    # Input constraints and parameters
    # Required stay durations (in days) for each city
    cities = {
        "Prague": 2,
        "Berlin": 3,
        "Tallinn": 5,
        "Stockholm": 5
    }
    # Total itinerary unique days (excluding overlaps) must be 12.
    total_days = 12

    # Available direct flight connections (treated as undirected)
    available_flights = {
        frozenset(["Berlin", "Tallinn"]),
        frozenset(["Prague", "Tallinn"]),
        frozenset(["Stockholm", "Tallinn"]),
        frozenset(["Prague", "Stockholm"]),
        frozenset(["Stockholm", "Berlin"])
    }
    
    # The rule: if a flight is taken on day X from A to B,
    # then the traveler is considered present in both A and B on day X.
    # In our itinerary, we structure the day assignments as segments.
    #
    # For a sequence of 4 segments with durations d1, d2, d3, d4,
    # let the segments be scheduled as follows:
    #   Segment 1: days 1 to d1.
    #   Segment 2: days d1 to (d1+d2-1). (Overlap on day d1)
    #   Segment 3: days (d1+d2-1) to (d1+d2+d3-2). (Overlap on day d1+d2-1)
    #   Segment 4: days (d1+d2+d3-2) to (d1+d2+d3+d4-3). (Overlap on day d1+d2+d3-2)
    # The total unique days = (d1+d2+d3+d4) - 3 must equal total_days.
    #
    # We now search for an itinerary order (a permutation of the 4 cities)
    # that satisfies:
    #   1. The computed total itinerary days equal 12.
    #   2. Consecutive segments can be connected by direct flights.
    #   3. The Berlin segment must include day 6 and day 8 (conference days).
    #   4. The Tallinn segment must include at least one day between day 8 and day 12 (for relatives).
    
    valid_plan = None

    for order in itertools.permutations(cities.keys()):
        segments = []  # each element: (city, start_day, end_day)
        current_day = 1
        for city in order:
            duration = cities[city]
            start_day = current_day
            end_day = start_day + duration - 1
            segments.append((city, start_day, end_day))
            # Next segment starts on the same day as the end_day (flight day overlap)
            current_day = end_day
        if current_day != total_days:
            continue

        # Check if each leg has a valid direct flight connection.
        flight_ok = True
        for i in range(len(segments) - 1):
            city_a = segments[i][0]
            city_b = segments[i+1][0]
            if frozenset([city_a, city_b]) not in available_flights:
                flight_ok = False
                break
        if not flight_ok:
            continue

        # Check Berlin conference constraint: Berlin must be present on day 6 and day 8.
        berlin_segment = next((seg for seg in segments if seg[0] == "Berlin"), None)
        if berlin_segment is None:
            continue
        b_start, b_end = berlin_segment[1], berlin_segment[2]
        if not (b_start <= 6 <= b_end and b_start <= 8 <= b_end):
            continue

        # Check Tallinn relatives constraint: at least one day in Tallinn between day 8 and day 12.
        tallinn_segment = next((seg for seg in segments if seg[0] == "Tallinn"), None)
        if tallinn_segment is None:
            continue
        t_start, t_end = tallinn_segment[1], tallinn_segment[2]
        # Compute intersection with [8, 12]
        inter_start = max(t_start, 8)
        inter_end = min(t_end, 12)
        if inter_start > inter_end:
            continue

        # If all constraints are met, we have a valid itinerary.
        valid_plan = segments
        break

    # Construct the JSON output.
    itinerary_list = []
    if valid_plan:
        for city, start, end in valid_plan:
            itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()