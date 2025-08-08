#!/usr/bin/env python3
import itertools
import json

def main():
    # Input trip constraints
    total_days = 17
    # Cities and required stay durations (in days)
    durations = {
        "Stuttgart": 2,
        "Bucharest": 2,
        "Geneva": 4,
        "Valencia": 6,
        "Munich": 7
    }
    cities = list(durations.keys())

    # Allowed direct flights between cities (bidirectional)
    allowed_flights = {
        frozenset(["Geneva", "Munich"]),
        frozenset(["Munich", "Valencia"]),
        frozenset(["Bucharest", "Valencia"]),
        frozenset(["Munich", "Bucharest"]),
        frozenset(["Valencia", "Stuttgart"]),
        frozenset(["Geneva", "Valencia"])
    }

    # Constraints: 
    # - Geneva must be visited such that at least one day is between Day 1 and Day 4.
    # - Munich must be visited such that at least one day is between Day 4 and Day 10.
    def satisfies_time_constraint(city, start, end):
        if city == "Geneva":
            # At least one day in Geneva is between Day 1 and Day 4.
            # So its stay must start no later than Day 4.
            if start > 4:
                return False
        if city == "Munich":
            # Munich should overlap with [4, 10].
            # Intersection exists if start <= 10 and end >= 4.
            if start > 10 or end < 4:
                return False
        return True

    valid_itinerary = None

    # Generate all possible permutations (orders) of the 5 cities.
    # We will check flight connectivity, compute day ranges, and check time constraints.
    for perm in itertools.permutations(cities):
        # Check that each consecutive city pair has a direct flight connection.
        route_valid = True
        for i in range(len(perm) - 1):
            if frozenset([perm[i], perm[i+1]]) not in allowed_flights:
                route_valid = False
                break
        if not route_valid:
            continue

        # Compute day ranges based on the rule:
        # The first city is visited from Day 1 to Day (duration_1).
        # When flying on a day X from city A to city B, that day counts for both.
        itinerary_segments = []
        current_start = 1
        for city in perm:
            d = durations[city]
            current_end = current_start + d - 1
            itinerary_segments.append((city, current_start, current_end))
            current_start = current_end  # next city's start is the same day as the previous city's end
        # Check if total schedule fits the overall total days.
        if itinerary_segments[-1][2] != total_days:
            continue

        # Check individual city time constraints.
        constraints_ok = True
        for city, start, end in itinerary_segments:
            if not satisfies_time_constraint(city, start, end):
                constraints_ok = False
                break
        if not constraints_ok:
            continue

        # If we reach here, this permutation is valid.
        valid_itinerary = itinerary_segments
        break

    # Prepare output JSON structure.
    if valid_itinerary is None:
        output = {"itinerary": []}
    else:
        itinerary_list = []
        for city, start, end in valid_itinerary:
            itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
        output = {"itinerary": itinerary_list}

    print(json.dumps(output))

if __name__ == "__main__":
    main()