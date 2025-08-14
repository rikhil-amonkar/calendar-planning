import itertools
import json

def main():
    cities = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
    durations = {
        'Prague': 4,
        'Stuttgart': 2,
        'Split': 2,
        'Krakow': 2,
        'Florence': 2
    }
    direct_flights = {
        'Stuttgart': ['Split', 'Krakow'],
        'Split': ['Stuttgart', 'Krakow', 'Prague'],
        'Krakow': ['Stuttgart', 'Split', 'Prague'],
        'Prague': ['Split', 'Krakow', 'Florence'],
        'Florence': ['Prague']
    }

    valid_paths = []
    for perm in itertools.permutations(cities):
        valid = True
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i + 1]
            if next_city not in direct_flights[current]:
                valid = False
                break
        if valid:
            valid_paths.append(perm)

    for path in valid_paths:
        day_ranges = []
        current_day = 1
        for city in path:
            duration = durations[city]
            end_day = current_day + duration - 1
            day_ranges.append({
                'city': city,
                'start': current_day,
                'end': end_day
            })
            current_day = end_day

        stuttgart_idx = path.index('Stuttgart')
        stuttgart_start = day_ranges[stuttgart_idx]['start']
        stuttgart_end = day_ranges[stuttgart_idx]['end']
        wedding_ok = (2 >= stuttgart_start and 2 <= stuttgart_end) or (3 >= stuttgart_start and 3 <= stuttgart_end)

        split_idx = path.index('Split')
        split_start = day_ranges[split_idx]['start']
        split_end = day_ranges[split_idx]['end']
        meeting_ok = (3 >= split_start and 3 <= split_end) or (4 >= split_start and 4 <= split_end)

        if wedding_ok and meeting_ok:
            itinerary = []
            for dr in day_ranges:
                day_range_str = f"Day {dr['start']}-{dr['end']}"
                itinerary.append({
                    'day_range': day_range_str,
                    'place': dr['city']
                })
            print(json.dumps({'itinerary': itinerary}))
            return

    print(json.dumps({'error': 'No valid itinerary found'}))

if __name__ == '__main__':
    main()