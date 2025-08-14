import itertools
import json

def main():
    cities = [
        {'name': 'Bucharest', 'duration': 3},
        {'name': 'Venice', 'duration': 5, 'fixed_window': (22, 26)},
        {'name': 'Prague', 'duration': 4},
        {'name': 'Frankfurt', 'duration': 5, 'fixed_window': (12, 16)},
        {'name': 'Zurich', 'duration': 5},
        {'name': 'Florence', 'duration': 5},
        {'name': 'Tallinn', 'duration': 5, 'fixed_window': (8, 12)},
    ]

    edges = {
        'Bucharest': ['Prague', 'Frankfurt', 'Zurich'],
        'Venice': ['Frankfurt', 'Zurich'],
        'Prague': ['Tallinn', 'Zurich', 'Florence', 'Bucharest', 'Frankfurt'],
        'Frankfurt': ['Bucharest', 'Venice', 'Prague', 'Zurich', 'Florence', 'Tallinn'],
        'Zurich': ['Prague', 'Frankfurt', 'Florence', 'Venice', 'Tallinn'],
        'Florence': ['Prague', 'Zurich', 'Frankfurt'],
        'Tallinn': ['Prague', 'Frankfurt', 'Zurich'],
    }

    # Generate all permutations of cities
    for perm in itertools.permutations(cities):
        valid = True
        # Check direct flights between consecutive cities
        for i in range(len(perm) - 1):
            current = perm[i]['name']
            next_city = perm[i+1]['name']
            if next_city not in edges[current]:
                valid = False
                break
        if not valid:
            continue

        # Compute day ranges
        day_ranges = []
        current_day = 1
        for city in perm:
            name = city['name']
            duration = city['duration']
            start_day = current_day
            end_day = start_day + duration - 1
            day_ranges.append({
                'name': name,
                'start': start_day,
                'end': end_day
            })
            current_day = end_day  # next city starts on this day

        # Check if total days is 26
        if current_day != 26:
            continue

        # Now check fixed windows
        valid = True
        for i in range(len(perm)):
            city = perm[i]
            if 'fixed_window' in city:
                start, end = city['fixed_window']
                dr = day_ranges[i]
                if dr['start'] != start or dr['end'] != end:
                    valid = False
                    break
        if not valid:
            continue

        # If we reach here, the permutation is valid
        # Generate the itinerary
        itinerary = []
        for dr in day_ranges:
            itinerary.append({
                'day_range': f"Day {dr['start']}-{dr['end']}",
                'place': dr['name']
            })
        print(json.dumps({"itinerary": itinerary}))
        return

    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()