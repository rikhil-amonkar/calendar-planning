#!/usr/bin/env python3
import itertools
import json

def compute_itinerary(order, durations):
    # Compute day intervals for each segment.
    # On each flight day, the day is counted for both cities.
    segments = []
    current_day = 1
    for i, city in enumerate(order):
        start_day = current_day
        end_day = start_day + durations[city] - 1
        segments.append({"city": city, "start": start_day, "end": end_day})
        # For all but the final segment, the flight day is shared so next segment starts on same day as current end_day.
        if i < len(order) - 1:
            current_day = end_day
    return segments

def is_valid_flights(order, flight_graph):
    # Check that each consecutive pair in the order has a direct flight (bidirectional assumed)
    for i in range(len(order) - 1):
        if order[i+1] not in flight_graph[order[i]]:
            return False
    return True

def main():
    # Input constraints
    total_trip_days = 16
    durations = {
        "Istanbul": 2,
        "Rome": 3,
        "Seville": 4,
        "Naples": 7,
        "Santorini": 4
    }
    # Flight connections: bidirectional edges
    flight_graph = {
        "Rome": {"Santorini", "Seville", "Naples", "Istanbul"},
        "Santorini": {"Rome", "Naples"},
        "Seville": {"Rome"},
        "Istanbul": {"Naples", "Rome"},
        "Naples": {"Istanbul", "Rome", "Santorini"}
    }
    # Special constraints:
    # - Istanbul: exactly 2 days and must be visited so that day 6 and day 7 are spent there.
    # - Santorini: exactly 4 days and must include day 13-16 (wedding).
    #
    # We have 5 unique cities. Santorini must be the last segment to meet the wedding day requirement.
    # We iterate over permutations of the other 4 cities and append Santorini at the end.
    other_cities = ["Istanbul", "Rome", "Seville", "Naples"]
    valid_solution = None

    for perm in itertools.permutations(other_cities):
        order = list(perm) + ["Santorini"]
        # Check flight connectivity between consecutive cities.
        if not is_valid_flights(order, flight_graph):
            continue

        segments = compute_itinerary(order, durations)
        # Verify total trip duration is exactly 16 days.
        if segments[-1]["end"] != total_trip_days:
            continue

        # Check Istanbul constraint: its segment must cover days 6 and 7 exactly.
        istanbul_ok = True
        for seg in segments:
            if seg["city"] == "Istanbul":
                # For a 2-day visit to cover days 6 and 7, the segment must start on day 6 (and end on day 7).
                if seg["start"] != 6 or seg["end"] != 7:
                    istanbul_ok = False
                break
        if not istanbul_ok:
            continue

        # Check Santorini constraint: as the last city, its segment must start at day 13 to cover 13-16.
        santorini_seg = segments[-1]
        if santorini_seg["city"] != "Santorini" or santorini_seg["start"] != 13 or santorini_seg["end"] != 16:
            continue

        valid_solution = segments
        break

    if valid_solution is None:
        result = {"itinerary": []}
    else:
        # Format output itinerary according to required structure.
        itinerary_output = []
        for seg in valid_solution:
            day_range = f"Day {seg['start']}-{seg['end']}"
            itinerary_output.append({"day_range": day_range, "place": seg["city"]})
        result = {"itinerary": itinerary_output}
    print(json.dumps(result))

if __name__ == "__main__":
    main()