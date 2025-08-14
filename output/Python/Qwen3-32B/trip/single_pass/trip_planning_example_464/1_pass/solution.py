import itertools
import json

def main():
    cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
    required_durations = {
        'Krakow': 5,
        'Frankfurt': 4,
        'Oslo': 3,
        'Dubrovnik': 5,
        'Naples': 5
    }
    # Define the direct flight connections (bidirectional)
    connections = set()
    connection_pairs = [
        ('Dubrovnik', 'Oslo'),
        ('Frankfurt', 'Krakow'),
        ('Frankfurt', 'Oslo'),
        ('Dubrovnik', 'Frankfurt'),
        ('Krakow', 'Oslo'),
        ('Naples', 'Oslo'),
        ('Naples', 'Dubrovnik'),
        ('Naples', 'Frankfurt')
    ]
    for a, b in connection_pairs:
        connections.add((a, b))
        connections.add((b, a))  # Add reverse direction

    # Generate all permutations of the cities
    for perm in itertools.permutations(cities):
        valid_sequence = True
        for i in range(len(perm)-1):
            if (perm[i], perm[i+1]) not in connections:
                valid_sequence = False
                break
        if not valid_sequence:
            continue

        # Calculate day ranges for each city in the permutation
        day_ranges = []
        current_start_day = 1
        for city in perm:
            duration = required_durations[city]
            end_day = current_start_day + duration - 1
            day_ranges.append((city, current_start_day, end_day))
            current_start_day = end_day  # flight happens on end_day, next city starts on that day

        # Check Dubrovnik and Oslo constraints
        dubrovnik_info = None
        oslo_info = None
        for city, start, end in day_ranges:
            if city == 'Dubrovnik':
                dubrovnik_info = (start, end)
            elif city == 'Oslo':
                oslo_info = (start, end)

        if dubrovnik_info and oslo_info:
            dub_start, dub_end = dubrovnik_info
            os_start, os_end = oslo_info
            if (dub_start <= 5 and dub_end >= 9) and (os_start == 16 and os_end == 18):
                # Found valid itinerary
                itinerary = []
                for city, start, end in day_ranges:
                    day_range_str = f"Day {start}-{end}"
                    itinerary.append({"day_range": day_range_str, "place": city})
                print(json.dumps({"itinerary": itinerary}))
                return

    # If no valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()