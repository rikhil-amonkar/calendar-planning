#!/usr/bin/env python3
import json
import itertools

def main():
    total_days = 12

    # Define the required days for each city.
    city_requirements = {
        "Hamburg": 2,
        "Zurich": 3,
        "Helsinki": 2,
        "Bucharest": 2,
        "Split": 7
    }
    cities = list(city_requirements.keys())

    # Define direct flight connections (bidirectional).
    flights_graph = {
        "Zurich": {"Helsinki", "Hamburg", "Bucharest", "Split"},
        "Helsinki": {"Zurich", "Hamburg", "Split"},
        "Hamburg": {"Zurich", "Bucharest", "Helsinki", "Split"},
        "Bucharest": {"Hamburg", "Zurich"},
        "Split": {"Zurich", "Helsinki", "Hamburg"}
    }

    # Special event constraints:
    # - Wedding in Zurich between day 1 and day 3.
    # - Conference in Split on day 4 and day 10.
    # Note: If you fly on day X, you count as being in both departure and arrival cities on that day.

    # Given an ordering of cities, compute the calendar segments.
    def compute_segments(order):
        segments = []
        start_day = 1
        for city in order:
            duration = city_requirements[city]
            end_day = start_day + duration - 1
            segments.append((city, start_day, end_day))
            # Next segment starts on the same day as the current segment's end (flight day overlap)
            start_day = end_day
        return segments

    # Checks if an ordering satisfies flight connectivity and special event constraints.
    def valid_itinerary(order):
        # Check flight connectivity for consecutive cities.
        for i in range(len(order) - 1):
            if order[i+1] not in flights_graph[order[i]]:
                return False

        segments = compute_segments(order)
        for city, start_day, end_day in segments:
            if city == "Zurich":
                # Wedding must be attended in Zurich between day 1 and day 3.
                # Therefore, Zurich's segment should intersect [1, 3] (i.e. start_day must be <= 3).
                if start_day > 3:
                    return False
            if city == "Split":
                # Conference in Split on day 4 and day 10
                # Split's segment must include day 4 and day 10.
                if start_day > 4 or end_day < 10:
                    return False
        return True

    valid_order = None
    for perm in itertools.permutations(cities):
        if valid_itinerary(perm):
            valid_order = perm
            break

    if valid_order is None:
        result = {"itinerary": []}
    else:
        segments = compute_segments(valid_order)
        itinerary_list = []
        for city, start_day, end_day in segments:
            itinerary_list.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
        result = {"itinerary": itinerary_list}

    print(json.dumps(result))

if __name__ == "__main__":
    main()