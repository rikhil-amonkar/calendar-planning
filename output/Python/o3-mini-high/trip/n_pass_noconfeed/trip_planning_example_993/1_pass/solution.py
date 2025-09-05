import json
import itertools

def main():
    # Define the cities and their required durations (in days)
    durations = {
        "Riga": 2,
        "Frankfurt": 3,
        "Amsterdam": 2,
        "Vilnius": 5,
        "London": 2,
        "Stockholm": 3,
        "Bucharest": 4
    }
    cities = list(durations.keys())
    
    # Special event time windows (inclusive):
    # Friend meeting in Amsterdam between day 2 and 3
    # Workshop in Vilnius between day 7 and 11
    # Wedding in Stockholm between day 13 and 15
    events = {
        "Amsterdam": (2, 3),
        "Vilnius": (7, 11),
        "Stockholm": (13, 15)
    }
    
    # Direct flight connections (bidirectional)
    flight_list = [
        ("London", "Amsterdam"),
        ("Vilnius", "Frankfurt"),
        ("Riga", "Vilnius"),       # from Riga to Vilnius
        ("Riga", "Stockholm"),
        ("London", "Bucharest"),
        ("Amsterdam", "Stockholm"),
        ("Amsterdam", "Frankfurt"),
        ("Frankfurt", "Stockholm"),
        ("Bucharest", "Riga"),
        ("Amsterdam", "Riga"),
        ("Amsterdam", "Bucharest"),
        ("Riga", "Frankfurt"),
        ("Bucharest", "Frankfurt"),
        ("London", "Frankfurt"),
        ("London", "Stockholm"),
        ("Amsterdam", "Vilnius")
    ]
    
    # Build a set of allowed flight edges (bidirectional)
    flights = set()
    for a, b in flight_list:
        flights.add((a, b))
        flights.add((b, a))
    
    # Total unique trip days are 15 (calculation: sum(durations)=21, 
    # but with overlapping flight days (6 overlaps) overall 21-6=15 days)
    total_days = 15
    
    valid_itinerary = None
    
    # Permute orderings of all 7 cities
    for perm in itertools.permutations(cities):
        # Check if direct flights exist between consecutive cities
        valid_flights = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in flights:
                valid_flights = False
                break
        if not valid_flights:
            continue
        
        # Compute the day ranges for each city segment.
        # If a flight is taken on day X, then that day counts for both cities.
        # We define for the first city: start_day = 1, end_day = start_day + duration - 1.
        # For every subsequent city, start_day = previous city's end_day (overlap) 
        # and end_day = start_day + duration - 1.
        segments = []
        current_day = 1
        for city in perm:
            seg_start = current_day
            seg_end = seg_start + durations[city] - 1
            segments.append((city, seg_start, seg_end))
            current_day = seg_end  # next segment starts on the same overlapping day
        # The overall trip must end on day 15.
        if segments[-1][2] != total_days:
            continue
        
        # Check that the event day windows are satisfied.
        event_ok = True
        for event_city, (req_start, req_end) in events.items():
            # Find the segment for the event city
            seg = next(( (s, e) for (c, s, e) in segments if c == event_city ), None)
            if seg is None:
                event_ok = False
                break
            seg_start, seg_end = seg
            # The city's day range must overlap with the event window.
            if seg_end < req_start or seg_start > req_end:
                event_ok = False
                break
        
        if not event_ok:
            continue
        
        # Found a valid itinerary; break and use it.
        valid_itinerary = segments
        break
    
    # Prepare the JSON output
    if valid_itinerary is None:
        output = {"itinerary": []}
    else:
        itinerary_output = []
        for city, start, end in valid_itinerary:
            itinerary_output.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
        output = {"itinerary": itinerary_output}
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()