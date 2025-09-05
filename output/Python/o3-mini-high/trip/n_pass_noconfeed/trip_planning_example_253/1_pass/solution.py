#!/usr/bin/env python3
import itertools
import json

def main():
    # Trip parameters
    total_days = 14
    # Required durations for each city
    durations = {
        "Amsterdam": 3,
        "Vienna": 7,
        "Santorini": 4,
        "Lyon": 3
    }
    # Event constraints with required windows (inclusive)
    # For Amsterdam: a workshop must be attended between Day 9 and Day 11.
    # For Lyon: a wedding must be attended between Day 7 and Day 9.
    events = {
        "Amsterdam": {"window": (9, 11)},
        "Lyon": {"window": (7, 9)}
    }
    # Allowed direct flight connections (symmetric)
    allowed_flights = {
        ("Vienna", "Lyon"),
        ("Vienna", "Santorini"),
        ("Vienna", "Amsterdam"),
        ("Amsterdam", "Santorini"),
        ("Lyon", "Amsterdam")
    }
    
    def flight_allowed(city1, city2):
        return (city1, city2) in allowed_flights or (city2, city1) in allowed_flights

    cities = list(durations.keys())
    valid_itinerary = None

    # Check all permutations of city orders
    for perm in itertools.permutations(cities):
        # Verify flight connectivity between consecutive cities
        valid_connection = True
        for i in range(len(perm) - 1):
            if not flight_allowed(perm[i], perm[i+1]):
                valid_connection = False
                break
        if not valid_connection:
            continue

        # Compute itinerary segments using the rule:
        # First city: Day 1 to (duration of first city)
        # For later cities, if the previous segment ends on day X, the next segment starts on day X (flight day overlap)
        segments = []
        current_start = 1
        for city in perm:
            dur = durations[city]
            current_end = current_start + dur - 1
            segments.append((city, current_start, current_end))
            current_start = current_end  # next segment starts on the same day as previous ended (flight overlap)

        # Verify that the complete itinerary spans exactly total_days days.
        if segments[-1][2] != total_days:
            continue

        # Check event constraints for cities with events.
        events_ok = True
        for city, start, end in segments:
            if city in events:
                event_start, event_end = events[city]["window"]
                # There must be an overlap between the city's days and the event window.
                if end < event_start or start > event_end:
                    events_ok = False
                    break
        if not events_ok:
            continue

        # If we reach here, this permutation satisfies flight connections and event constraints.
        valid_itinerary = segments
        break

    # Format the valid itinerary into the required JSON structure.
    output = {"itinerary": []}
    if valid_itinerary:
        for city, start, end in valid_itinerary:
            segment = {"day_range": f"Day {start}-{end}", "place": city}
            output["itinerary"].append(segment)

    print(json.dumps(output))

if __name__ == "__main__":
    main()