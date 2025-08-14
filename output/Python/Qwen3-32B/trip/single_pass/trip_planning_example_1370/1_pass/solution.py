import itertools
import json

def main():
    cities = [
        {'name': 'Paris', 'duration': 4, 'constraint': (11, 15)},
        {'name': 'Krakow', 'duration': 4, 'constraint': (18, 22)},
        {'name': 'Santorini', 'duration': 4, 'constraint': (25, 29)},
        {'name': 'Vilnius', 'duration': 2, 'constraint': None},
        {'name': 'Munich', 'duration': 4, 'constraint': None},
        {'name': 'Geneva', 'duration': 2, 'constraint': None},
        {'name': 'Amsterdam', 'duration': 4, 'constraint': None},
        {'name': 'Budapest', 'duration': 4, 'constraint': None},
        {'name': 'Split', 'duration': 2, 'constraint': None},
    ]

    city_names = [city['name'] for city in cities]
    direct_flights = {
        'Paris': ['Krakow', 'Amsterdam', 'Split', 'Geneva', 'Budapest', 'Munich'],
        'Krakow': ['Paris', 'Split', 'Munich', 'Amsterdam', 'Vilnius'],
        'Amsterdam': ['Paris', 'Geneva', 'Munich', 'Budapest', 'Split', 'Krakow', 'Vilnius', 'Santorini'],
        'Split': ['Paris', 'Amsterdam', 'Krakow', 'Geneva', 'Munich'],
        'Vilnius': ['Munich', 'Krakow', 'Amsterdam', 'Paris'],
        'Munich': ['Vilnius', 'Split', 'Geneva', 'Amsterdam', 'Budapest', 'Krakow', 'Paris'],
        'Geneva': ['Paris', 'Amsterdam', 'Split', 'Munich', 'Budapest', 'Santorini'],
        'Budapest': ['Amsterdam', 'Munich', 'Geneva', 'Paris'],
        'Santorini': ['Geneva', 'Amsterdam'],
    }

    total_days = 30

    for perm in itertools.permutations(city_names):
        valid_path = True
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i+1]
            if next_city not in direct_flights[current]:
                valid_path = False
                break
        if not valid_path:
            continue

        sum_d_minus_1 = sum(city['duration'] - 1 for city in cities)
        s1 = total_days - sum_d_minus_1

        if s1 < 1:
            continue

        current_start = s1
        constraint_satisfied = True
        itinerary_days = []
        for city_name in perm:
            city = next(c for c in cities if c['name'] == city_name)
            duration = city['duration']
            constraint = city['constraint']
            end_day = current_start + duration - 1
            if constraint:
                start_window, end_window = constraint
                if not (current_start <= end_window and end_day >= start_window):
                    constraint_satisfied = False
                    break
            itinerary_days.append({
                'city': city_name,
                'start': current_start,
                'end': end_day
            })
            current_start = end_day

        if not constraint_satisfied:
            continue

        itinerary = []
        for entry in itinerary_days:
            start = entry['start']
            end = entry['end']
            day_range = f"Day {start}-Day {end}"
            city = entry['city']
            itinerary.append({'day_range': day_range, 'place': city})

        print(json.dumps({'itinerary': itinerary}))
        return

    print(json.dumps({'error': 'No valid itinerary found'}))

if __name__ == "__main__":
    main()