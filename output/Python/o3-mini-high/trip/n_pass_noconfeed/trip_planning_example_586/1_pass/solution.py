import json
import itertools

def main():
    # Total trip days
    total_days = 12

    # Define the cities and the required durations (in days) to be spent in each city.
    durations = {
        "Frankfurt": 3,
        "Naples": 4,
        "Helsinki": 4,
        "Lyon": 3,
        "Prague": 2
    }
    cities = list(durations.keys())

    # Define event constraints:
    # - There is a workshop in Prague that must be attended between Day 1 and Day 2.
    # - There is an annual show in Helsinki that must be attended from Day 2 to Day 5.
    workshop_city = "Prague"
    workshop_window = (1, 2)  # workshop must fall within this range
    show_city = "Helsinki"
    show_window = (2, 5)      # show must fall within this range

    # Define direct flight connections (bidirectional flights)
    flights = set([
        frozenset(["Prague", "Lyon"]),
        frozenset(["Prague", "Frankfurt"]),
        frozenset(["Frankfurt", "Lyon"]),
        frozenset(["Helsinki", "Naples"]),
        frozenset(["Helsinki", "Frankfurt"]),
        frozenset(["Naples", "Frankfurt"]),
        frozenset(["Prague", "Helsinki"])
    ])

    # To satisfy the event constraints, we fix that the itinerary must start in Prague (for the workshop)
    # and have Helsinki as the second city (to cover the show from Day 2 to Day 5).
    fixed_start = "Prague"
    fixed_second = "Helsinki"
    remaining_cities = [city for city in cities if city not in (fixed_start, fixed_second)]
    
    found_itinerary = None

    # Try all permutations of the remaining three cities.
    for perm in itertools.permutations(remaining_cities):
        itinerary_order = [fixed_start, fixed_second] + list(perm)
        
        # Check that each flight between consecutive cities is direct.
        valid = True
        for i in range(len(itinerary_order) - 1):
            if frozenset([itinerary_order[i], itinerary_order[i + 1]]) not in flights:
                valid = False
                break
        if not valid:
            continue

        # Compute the timeline intervals.
        # When flying on day X, you are counted as being in both the origin and destination cities.
        # We'll assign the interval for the first city starting at Day 1.
        timeline = []
        current_day = 1
        for index, city in enumerate(itinerary_order):
            duration = durations[city]
            start = current_day
            end = current_day + duration - 1
            timeline.append((start, end))
            # For all except the last city, the flight occurs on the last day (overlap) so next city starts on "end".
            if index < len(itinerary_order) - 1:
                current_day = end

        # Verify that the final city's end day equals total_days.
        if timeline[-1][1] != total_days:
            continue

        # Check event constraints.
        # Workshop in Prague must be within its allocated time in the itinerary.
        prague_index = itinerary_order.index(workshop_city)
        prague_interval = timeline[prague_index]
        if not (workshop_window[0] >= prague_interval[0] and workshop_window[1] <= prague_interval[1]):
            continue

        # Annual show in Helsinki must be within its allocated time.
        helsinki_index = itinerary_order.index(show_city)
        helsinki_interval = timeline[helsinki_index]
        if not (show_window[0] >= helsinki_interval[0] and show_window[1] <= helsinki_interval[1]):
            continue

        # If all constraints are satisfied, take this itinerary.
        found_itinerary = (itinerary_order, timeline)
        break

    # Prepare the result in the required JSON structure.
    if found_itinerary is None:
        result = {"itinerary": []}
    else:
        itinerary_order, timeline = found_itinerary
        itinerary_list = []
        for city, (start, end) in zip(itinerary_order, timeline):
            itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
        result = {"itinerary": itinerary_list}

    print(json.dumps(result))

if __name__ == "__main__":
    main()