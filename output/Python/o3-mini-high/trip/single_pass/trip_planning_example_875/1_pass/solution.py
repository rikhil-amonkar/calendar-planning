#!/usr/bin/env python3
import itertools
import json

def main():
    # Input variables: cities with required durations and constraints.
    # Each city's "duration" is the number of days that must be spent there.
    # Note: if a flight is taken on a transition day, that day counts for both cities.
    cities_info = {
        "Stuttgart": {
            "duration": 3,
            "constraints": { "workshop": (11, 13) }  # Must be in Stuttgart on at least one day between 11 and 13.
        },
        "Edinburgh": {
            "duration": 4
        },
        "Athens": {
            "duration": 4
        },
        "Split": {
            "duration": 2,
            "constraints": { "meeting_split": (13, 14) }  # Must meet friends in Split on a day between 13 and 14.
        },
        "Krakow": {
            "duration": 4,
            "constraints": { "meeting_krakow": (8, 11) }  # Must meet a friend in Krakow on a day between 8 and 11.
        },
        "Venice": {
            "duration": 5
        },
        "Mykonos": {
            "duration": 4
        }
    }

    # Total calendar days available (taking into account overlapping flight days).
    total_calendar_days = 20

    # Define direct flight connections (assumed bidirectional).
    # Each connection is represented as a frozenset of two cities.
    flights = {
        frozenset(["Krakow", "Split"]),
        frozenset(["Split", "Athens"]),
        frozenset(["Edinburgh", "Krakow"]),
        frozenset(["Venice", "Stuttgart"]),
        frozenset(["Krakow", "Stuttgart"]),
        frozenset(["Edinburgh", "Stuttgart"]),
        frozenset(["Stuttgart", "Athens"]),
        frozenset(["Venice", "Edinburgh"]),
        frozenset(["Athens", "Mykonos"]),
        frozenset(["Venice", "Athens"]),
        frozenset(["Stuttgart", "Split"]),
        frozenset(["Edinburgh", "Athens"])
    }

    cities = list(cities_info.keys())
    valid_itinerary = None

    # Iterate over all permutations and select the first one that meets direct flight and date constraints.
    for perm in itertools.permutations(cities):
        # Check that each consecutive city pair is connected by a direct flight.
        valid_route = True
        for i in range(len(perm)-1):
            if frozenset([perm[i], perm[i+1]]) not in flights:
                valid_route = False
                break
        if not valid_route:
            continue

        # Compute the schedule.
        # The scheduling rule is: first city starts on day 1.
        # For each subsequent city, the start day equals the previous city's end day.
        # If a city has duration d, its days are from start_day to (start_day + d - 1) inclusive.
        schedule = []  # List of tuples: (city, start_day, end_day)
        current_day = 1
        for city in perm:
            duration = cities_info[city]["duration"]
            start_day = current_day
            end_day = current_day + duration - 1
            schedule.append((city, start_day, end_day))
            # Next city starts on the same day as this segment's end_day (overlap due to flight)
            current_day = end_day

        # Verify that the overall itinerary fits in total_calendar_days.
        if schedule[-1][2] != total_calendar_days:
            continue  # Should not happen given fixed durations.

        # Check specific city constraints.
        constraints_ok = True
        for city, start_day, end_day in schedule:
            if "constraints" in cities_info[city]:
                for key, (req_start, req_end) in cities_info[city]["constraints"].items():
                    # The city's segment days must intersect with the required day range.
                    # If there is no overlap then the constraint is not met.
                    if end_day < req_start or start_day > req_end:
                        constraints_ok = False
                        break
            if not constraints_ok:
                break

        if not constraints_ok:
            continue

        # If we reach here, we found a valid itinerary.
        valid_itinerary = schedule
        break

    # Format the itinerary for output.
    output = {"itinerary": []}
    if valid_itinerary is not None:
        for city, start, end in valid_itinerary:
            day_range_str = f"Day {start}-{end}"
            output["itinerary"].append({"day_range": day_range_str, "place": city})
    else:
        output["itinerary"] = []

    print(json.dumps(output))

if __name__ == "__main__":
    main()