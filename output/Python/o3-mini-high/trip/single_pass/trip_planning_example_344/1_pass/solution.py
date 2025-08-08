#!/usr/bin/env python3
import json
import itertools

def main():
    # Total trip days
    total_days = 20

    # Required durations for each city (in days)
    durations = {
        "Valencia": 6,
        "Athens": 6,
        "Naples": 5,
        "Zurich": 6
    }
    
    # Allowed direct flight connections.
    # Note: "Valencia and Naples", "Athens and Naples", "Zurich and Naples",
    # "Athens and Zurich", and "Zurich and Valencia" are bidirectional.
    # "from Valencia to Athens" is only allowed in that direction.
    allowed_flights = {
        "Athens": ["Naples", "Zurich"],
        "Naples": ["Valencia", "Athens", "Zurich"],
        "Valencia": ["Naples", "Athens", "Zurich"],
        "Zurich": ["Naples", "Athens", "Valencia"]
    }
    
    # Special trip constraints:
    # - Visit relatives in Athens between day 1 and day 6
    # - Attend a wedding in Naples between day 16 and day 20
    relatives_interval = (1, 6)  # inclusive interval for Athens relatives visit
    wedding_interval = (16, 20)  # inclusive interval for Naples wedding

    # Cities to visit (order to be determined)
    cities = list(durations.keys())  # ["Valencia", "Athens", "Naples", "Zurich"]

    valid_itinerary = None

    # We'll evaluate all permutations and pick one that meets:
    # 1. Flight connectivity between consecutive cities.
    # 2. The total trip length is exactly total_days (accounting for overlap on flight days).
    # 3. Athens segment overlaps with [1,6] and Naples segment overlaps with [16,20].
    # 4. For optimality, we enforce that Athens is visited first and Naples last.
    for perm in itertools.permutations(cities):
        # Enforce optimal ordering: Athens must be the first city and Naples the last.
        if perm[0] != "Athens" or perm[-1] != "Naples":
            continue

        segments = []
        current_day = 1
        # Compute day ranges for each city.
        for i, city in enumerate(perm):
            if i == 0:
                start_day = current_day
                end_day = current_day + durations[city] - 1
            else:
                # Flight day: traveler is in both cities on this day.
                start_day = current_day
                end_day = start_day + durations[city] - 1
            segments.append((city, start_day, end_day))
            current_day = end_day
        # Verify the complete trip covers exactly total_days.
        if current_day != total_days:
            continue

        # Check direct flight connectivity between cities.
        flight_possible = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in allowed_flights.get(perm[i], []):
                flight_possible = False
                break
        if not flight_possible:
            continue

        # Check special constraints for Athens (relatives visit) and Naples (wedding)
        constraints_ok = True
        for city, start_day, end_day in segments:
            if city == "Athens":
                # There must be at least one day in Athens falling between day 1 and day 6.
                if max(start_day, relatives_interval[0]) > min(end_day, relatives_interval[1]):
                    constraints_ok = False
                    break
            if city == "Naples":
                # There must be at least one day in Naples between day 16 and day 20.
                if max(start_day, wedding_interval[0]) > min(end_day, wedding_interval[1]):
                    constraints_ok = False
                    break
        if not constraints_ok:
            continue

        # If we reached here, this itinerary meets all constraints.
        valid_itinerary = segments
        break

    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        for city, start_day, end_day in valid_itinerary:
            day_range = f"Day {start_day}-{end_day}"
            itinerary_list.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_list}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()