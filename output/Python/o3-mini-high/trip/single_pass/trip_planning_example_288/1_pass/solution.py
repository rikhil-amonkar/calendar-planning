#!/usr/bin/env python3
import json
import itertools

def main():
    # Input trip constraints
    total_trip_days = 15
    durations = {
        "Stuttgart": 5,
        "Manchester": 7,
        "Madrid": 4,
        "Vienna": 2
    }
    # Constraints for events:
    wedding_window = (1, 7)    # Manchester wedding must occur between Day 1 and Day 7
    workshop_window = (11, 15) # Stuttgart workshop must occur between Day 11 and Day 15

    # Direct flight connections (bidirectional)
    flight_graph = {
        "Manchester": ["Vienna", "Stuttgart", "Madrid"],
        "Stuttgart": ["Vienna", "Manchester"],
        "Madrid": ["Vienna", "Manchester"],
        "Vienna": ["Stuttgart", "Manchester", "Madrid"]
    }

    # All cities to visit
    cities = ["Manchester", "Stuttgart", "Madrid", "Vienna"]
    # Since the wedding in Manchester must occur within Day 1-7,
    # force Manchester to be the first city.
    remaining_cities = [city for city in cities if city != "Manchester"]
    
    valid_route = None
    valid_timelines = None

    # Try all orders of the remaining three cities appended after Manchester.
    for perm in itertools.permutations(remaining_cities):
        route = ["Manchester"] + list(perm)
        # Check direct flights between consecutive cities.
        valid_flights = True
        for i in range(len(route) - 1):
            if route[i+1] not in flight_graph[route[i]]:
                valid_flights = False
                break
        if not valid_flights:
            continue

        # Compute the day ranges using the rule:
        # First city starts on Day 1 with duration d, so covers Day 1 through d.
        # For subsequent segments, if flight is taken on day X, then the next city's segment starts on day X.
        timelines = []
        current_start = 1
        for city in route:
            current_end = current_start + durations[city] - 1
            timelines.append((current_start, current_end))
            # Flight day overlap: next segment starts on the same day the previous segment ended.
            current_start = current_end

        # Check total trip days.
        if timelines[-1][1] != total_trip_days:
            continue  # not matching 15 days total

        # Check wedding constraint in Manchester (must have at least one day within Day 1-7).
        manchester_range = timelines[0]
        # (Since Manchester is first and has duration 7, its day range should be Day 1-7.)
        if not (wedding_window[0] >= manchester_range[0] and wedding_window[1] <= manchester_range[1] or
                (manchester_range[0] <= wedding_window[1] and manchester_range[1] >= wedding_window[0])):
            continue

        # Check workshop constraint in Stuttgart (must have at least one day within Day 11-15).
        if "Stuttgart" not in route:
            continue
        stuttgart_index = route.index("Stuttgart")
        stuttgart_range = timelines[stuttgart_index]
        # Check if Stuttgart's day range intersects with workshop window.
        if stuttgart_range[1] < workshop_window[0] or stuttgart_range[0] > workshop_window[1]:
            continue

        # If all constraints are satisfied, we've found a valid route.
        valid_route = route
        valid_timelines = timelines
        break

    # Prepare output itinerary as a list of segments.
    itinerary = []
    if valid_route and valid_timelines:
        for idx, city in enumerate(valid_route):
            start_day, end_day = valid_timelines[idx]
            itinerary.append({
                "day_range": "Day {}-{}".format(start_day, end_day),
                "place": city
            })
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()