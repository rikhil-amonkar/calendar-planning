#!/usr/bin/env python3
import itertools
import json

def compute_schedule(order, durations):
    schedule = []
    current_day = 1
    for i, city in enumerate(order):
        start = current_day
        dur = durations[city]
        # The traveler spends 'dur' days in the city.
        # Except the first city, the arrival day is shared with the previous city.
        end = start + dur - 1
        schedule.append((city, start, end))
        # For all but the last segment, the flight on the end day overlaps.
        if i < len(order) - 1:
            current_day = end  # next city starts on the same flight day
        else:
            current_day = end
    return schedule

def route_has_valid_flights(order, allowed_flights):
    # Check that each consecutive pair in the order has a direct flight
    for a, b in zip(order, order[1:]):
        if frozenset([a, b]) not in allowed_flights:
            return False
    return True

def schedule_meets_windows(schedule, windows):
    # For cities with specific day-window constraints, check that the entire stay falls within the window.
    for city, start, end in schedule:
        if city in windows:
            win_start, win_end = windows[city]
            if start < win_start or end > win_end:
                return False
    return True

def main():
    # Input variables
    total_days = 12
    # Required days in each city (as given in the problem)
    durations = {
        "Split": 2,
        "Helsinki": 2,
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6
    }
    # Window constraints: For Vilnius, visit relatives between day 7 and day 9.
    # For Reykjavik, attend a wedding between day 10 and day 12.
    windows = {
        "Vilnius": (7, 9),
        "Reykjavik": (10, 12)
    }
    # Allowed direct flights (bidirectional) between cities.
    allowed_flights = {
        frozenset(["Split", "Helsinki"]),
        frozenset(["Geneva", "Split"]),
        frozenset(["Geneva", "Helsinki"]),
        frozenset(["Helsinki", "Reykjavik"]),
        frozenset(["Vilnius", "Helsinki"]),
        frozenset(["Split", "Vilnius"])
    }
    
    cities = list(durations.keys())
    valid_itinerary = None

    # Try all orderings and choose the first one that meets all the constraints.
    for order in itertools.permutations(cities):
        if not route_has_valid_flights(order, allowed_flights):
            continue
        schedule = compute_schedule(order, durations)
        # With the given durations, total itinerary days = sum(durations) - (number of transitions)
        # It must equal total_days.
        if schedule[-1][2] != total_days:
            continue
        if not schedule_meets_windows(schedule, windows):
            continue
        valid_itinerary = schedule
        break

    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        # Build a list of dictionaries with day_range and place.
        for city, start, end in valid_itinerary:
            day_range = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_list}

    print(json.dumps(result))

if __name__ == "__main__":
    main()