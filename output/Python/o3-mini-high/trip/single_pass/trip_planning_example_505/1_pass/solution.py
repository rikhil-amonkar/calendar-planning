#!/usr/bin/env python3
import json
import itertools

def compute_schedule(order, durations):
    segments = []
    day = 1
    for city in order:
        start_day = day
        # The city requires durations[city] days.
        # When flying to the next city, the flight day counts for both cities.
        end_day = start_day + durations[city] - 1
        segments.append((city, start_day, end_day))
        day = end_day  # next city’s arrival day is the previous city’s end day (overlap)
    return segments

def event_in_segment(segment, event_days):
    # Check if any event day falls within the segment [start, end]
    _, start, end = segment
    for d in event_days:
        if start <= d <= end:
            return True
    return False

def main():
    # Input constraints
    total_days = 8
    cities = ["Prague", "Stuttgart", "Split", "Krakow", "Florence"]
    durations = {
        "Prague": 4,
        "Stuttgart": 2,
        "Split": 2,
        "Krakow": 2,
        "Florence": 2,
    }
    # Wedding in Stuttgart must be attended between Day 2 and Day 3.
    wedding_event_days = {2, 3}
    # Meeting friends in Split between Day 3 and Day 4.
    meeting_event_days = {3, 4}
    
    # Allowed direct flights (bidirectional)
    allowed_flights = {
        ("Stuttgart", "Split"),
        ("Prague", "Florence"),
        ("Krakow", "Stuttgart"),
        ("Krakow", "Split"),
        ("Split", "Prague"),
        ("Krakow", "Prague"),
    }
    flights = set()
    for (a, b) in allowed_flights:
        flights.add((a, b))
        flights.add((b, a))
    
    optimal_itinerary = None

    # Try all permutations of city visits.
    for perm in itertools.permutations(cities):
        valid_path = True
        # Check if every flight between adjacent cities exists.
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in flights:
                valid_path = False
                break
        if not valid_path:
            continue
        
        # Compute schedule segments for the order.
        segments = compute_schedule(perm, durations)
        # The last segment's end day must equal total_days.
        if segments[-1][2] != total_days:
            continue
        
        # Check event constraints.
        stuttgart_segment = None
        split_segment = None
        for seg in segments:
            if seg[0] == "Stuttgart":
                stuttgart_segment = seg
            if seg[0] == "Split":
                split_segment = seg
        if stuttgart_segment is None or split_segment is None:
            continue
        if not event_in_segment(stuttgart_segment, wedding_event_days):
            continue
        if not event_in_segment(split_segment, meeting_event_days):
            continue
        
        # If all conditions are met, build the itinerary.
        optimal_itinerary = []
        for city, start, end in segments:
            day_range = "Day {}-{}".format(start, end)
            optimal_itinerary.append({"day_range": day_range, "place": city})
        break

    if optimal_itinerary is None:
        result = {"itinerary": "No valid itinerary found"}
    else:
        result = {"itinerary": optimal_itinerary}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()