import itertools
import json

def main():
    cities = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
    durations = {
        'Amsterdam': 3,
        'Vienna': 7,
        'Santorini': 4,
        'Lyon': 3
    }
    allowed_flights = {
        ('Vienna', 'Lyon'),
        ('Lyon', 'Vienna'),
        ('Vienna', 'Santorini'),
        ('Santorini', 'Vienna'),
        ('Vienna', 'Amsterdam'),
        ('Amsterdam', 'Vienna'),
        ('Amsterdam', 'Santorini'),
        ('Santorini', 'Amsterdam'),
        ('Lyon', 'Amsterdam'),
        ('Amsterdam', 'Lyon'),
    }
    event_constraints = {
        'Lyon': (7, 9),
        'Amsterdam': (9, 11)
    }

    for perm in itertools.permutations(cities):
        # Check transitions between consecutive cities
        valid_transitions = True
        for i in range(len(perm) - 1):
            current, next_city = perm[i], perm[i+1]
            if (current, next_city) not in allowed_flights:
                valid_transitions = False
                break
        if not valid_transitions:
            continue

        # Compute day ranges
        day_ranges = []
        start_day = 1
        for city in perm:
            dur = durations[city]
            end_day = start_day + dur - 1
            day_ranges.append((city, (start_day, end_day)))
            start_day = end_day  # Corrected here

        # Check event constraints
        valid_events = True
        for city, (event_start, event_end) in event_constraints.items():
            found = False
            for (c, (s, e)) in day_ranges:
                if c == city:
                    # Check if [s, e] overlaps with [event_start, event_end]
                    if not (s <= event_end and e >= event_start):
                        valid_events = False
                        break
                    found = True
                    break
            if not found or not valid_events:
                break
        if valid_events:
            # Build the itinerary
            itinerary = []
            for (city, (s, e)) in day_ranges:
                day_range_str = f"Day {s}-{e}"
                itinerary.append({"day_range": day_range_str, "place": city})
            print(json.dumps({"itinerary": itinerary}))
            return

main()