#!/usr/bin/env python3
import json
import itertools

def main():
    # Input constraints and parameters
    total_days = 14
    
    # Required duration (in days) to be spent per city.
    durations = {
        "Amsterdam": 3,
        "Vienna": 7,
        "Santorini": 4,
        "Lyon": 3
    }
    
    # Event time windows (inclusive)
    # Amsterdam workshop must occur between day 9 and day 11.
    amsterdam_event_window = (9, 11)
    # Lyon wedding must occur between day 7 and day 9.
    lyon_event_window = (7, 9)
    
    # List of cities.
    cities = list(durations.keys())
    
    # Allowed direct flights (treated as undirected edges).
    # Each flight is represented as a frozenset of the two cities.
    allowed_flights = {
        frozenset(["Vienna", "Lyon"]),
        frozenset(["Vienna", "Santorini"]),
        frozenset(["Vienna", "Amsterdam"]),
        frozenset(["Amsterdam", "Santorini"]),
        frozenset(["Lyon", "Amsterdam"])
    }
    
    # Helper function to check if flight exists between two cities.
    def flight_possible(city1, city2):
        return frozenset([city1, city2]) in allowed_flights

    # Given a permutation (order) of cities, compute itinerary segments.
    # Each segment is a tuple: (city, start_day, end_day).
    # Flight days overlap: if you fly on the transition day, that day counts to both cities.
    def compute_itinerary(order):
        itinerary = []
        current_day = 1
        for city in order:
            start_day = current_day
            # The required duration for a city is counted on its arrival day + subsequent days.
            # When departing, the flight day is shared with the next city.
            end_day = start_day + durations[city] - 1
            itinerary.append((city, start_day, end_day))
            # Next city starts on the same day as the flight (end_day is overlapping).
            current_day = end_day
        return itinerary

    # Check if a given day-range [start, end] intersects with an event window [ev_start, ev_end]
    def event_in_range(start, end, ev_start, ev_end):
        return start <= ev_end and end >= ev_start

    valid_itinerary = None

    # We expect 4 cities and exactly 3 flights (each flight day overlaps)
    # Total itinerary days is sum(durations) - number_of_flights = 17 - 3 = 14.
    # Iterate over all permutations to find an order that satisfies:
    #   1. Each adjacent pair must have a direct flight.
    #   2. The itinerary day ranges for Amsterdam and Lyon intersect with their event windows.
    for order in itertools.permutations(cities):
        # Check if flights between adjacent cities are allowed.
        valid_flights = True
        for i in range(len(order)-1):
            if not flight_possible(order[i], order[i+1]):
                valid_flights = False
                break
        if not valid_flights:
            continue

        itinerary = compute_itinerary(order)
        
        # After computing, the last segment's end_day should equal total_days.
        if itinerary[-1][2] != total_days:
            continue

        # Check event constraints:
        event_ok = True
        for city, start, end in itinerary:
            if city == "Amsterdam":
                # Must have at least one day between day 9 and day 11.
                if not event_in_range(start, end, amsterdam_event_window[0], amsterdam_event_window[1]):
                    event_ok = False
                    break
            if city == "Lyon":
                # Must have at least one day between day 7 and day 9.
                if not event_in_range(start, end, lyon_event_window[0], lyon_event_window[1]):
                    event_ok = False
                    break
        if not event_ok:
            continue

        # If we reach here, we found a valid itinerary.
        valid_itinerary = itinerary
        break

    output = {}
    itinerary_list = []
    if valid_itinerary is None:
        output["itinerary"] = []
    else:
        # Build output structure. Each segment is represented as:
        # { "day_range": "Day X-Y", "place": "City" }
        for segment in valid_itinerary:
            city, start, end = segment
            itinerary_list.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
        output["itinerary"] = itinerary_list

    print(json.dumps(output))

if __name__ == '__main__':
    main()