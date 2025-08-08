#!/usr/bin/env python3
import json

def main():
    # Trip constraints input as variables
    # Cities with required stay durations and (optional) event windows.
    # Event windows are defined as (start_day, end_day) inclusive.
    cities = {
        "Salzburg": {"duration": 2, "event": None},          # no specific event
        "Venice": {"duration": 5, "event": None},
        "Bucharest": {"duration": 4, "event": None},
        "Brussels": {"duration": 2, "event": (21, 22)},        # meet friends between day 21 and 22
        "Hamburg": {"duration": 4, "event": None},
        "Copenhagen": {"duration": 4, "event": (18, 21)},      # wedding between day 18 and 21
        "Nice": {"duration": 3, "event": (9, 11)},             # visit relatives between day 9 and 11
        "Zurich": {"duration": 5, "event": None},
        "Naples": {"duration": 4, "event": (22, 25)}           # workshop between day 22 and 25
    }
    # Direct flight connections (undirected graph)
    flight_graph = {
        "Zurich": {"Brussels", "Naples", "Copenhagen", "Nice", "Venice", "Bucharest", "Hamburg"},
        "Brussels": {"Zurich", "Venice", "Bucharest", "Hamburg", "Nice", "Naples", "Copenhagen"},
        "Bucharest": {"Copenhagen", "Brussels", "Naples", "Hamburg", "Zurich"},
        "Venice": {"Brussels", "Naples", "Copenhagen", "Zurich", "Nice", "Hamburg"},
        "Nice": {"Zurich", "Hamburg", "Brussels", "Naples", "Venice", "Copenhagen"},
        "Hamburg": {"Nice", "Bucharest", "Brussels", "Copenhagen", "Venice", "Zurich", "Salzburg"},
        "Copenhagen": {"Bucharest", "Zurich", "Venice", "Hamburg", "Naples", "Brussels", "Nice"},
        "Salzburg": {"Hamburg"},
        "Naples": {"Zurich", "Venice", "Bucharest", "Brussels", "Copenhagen", "Nice"}
    }
    total_trip_days = 25
    num_cities = len(cities)
    
    # Backtracking search to compute a valid itinerary.
    # We define each itinerary entry as a tuple: (city, arrival_day, departure_day)
    # Rule: For the first city, arrival_day is 1.
    # When flying from city A to city B on day X, day X counts for both cities.
    # Thus, if a city has a required duration d, its interval is [arrival, arrival + d - 1],
    # and the next city’s arrival day is the same as the previous city’s departure day.
    def backtrack(path, current_day, used):
        # If all cities have been scheduled, check that the final departure equals total_trip_days.
        if len(path) == num_cities:
            # The departure day of the last city is already computed in the last tuple.
            # It must equal total_trip_days.
            if current_day == total_trip_days:
                return path
            else:
                return None
        
        # Iterate over cities in sorted order (to have reproducible output)
        for city in sorted(cities.keys()):
            if city in used:
                continue
            # If there is already a city in the itinerary, check flight connectivity from the last city.
            if path:
                last_city = path[-1][0]
                if city not in flight_graph[last_city]:
                    continue
            duration = cities[city]["duration"]
            start = current_day
            end = current_day + duration - 1
            # Check event constraint (if any): the city's interval [start, end] must intersect its event window.
            event = cities[city]["event"]
            if event is not None:
                event_start, event_end = event
                # No intersection if the stay ends before the event window starts or starts after it ends.
                if end < event_start or start > event_end:
                    continue
            # Prune search: compute minimum additional days needed for the remaining cities.
            remaining = [c for c in cities if c not in used and c != city]
            min_additional = sum(cities[c]["duration"] - 1 for c in remaining)
            # The final departure day if we choose this city and then add the minimum possible days
            if end + min_additional > total_trip_days:
                continue
            # Build new path and mark this city as used.
            new_path = path + [(city, start, end)]
            new_used = used.union({city})
            result = backtrack(new_path, end, new_used)
            if result is not None:
                return result
        return None

    solution = backtrack([], 1, set())
    
    # Format the solution into the required JSON output.
    itinerary = []
    if solution is not None:
        for city, arrival, departure in solution:
            day_range = "Day {}-{}".format(arrival, departure)
            itinerary.append({"day_range": day_range, "place": city})
    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()