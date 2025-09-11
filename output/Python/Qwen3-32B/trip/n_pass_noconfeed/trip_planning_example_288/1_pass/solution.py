import itertools
import json

def main():
    required_durations = {
        'Manchester': 7,
        'Stuttgart': 5,
        'Madrid': 4,
        'Vienna': 2
    }

    flights = {
        'Manchester': ['Vienna', 'Stuttgart', 'Madrid'],
        'Vienna': ['Manchester', 'Stuttgart', 'Madrid'],
        'Stuttgart': ['Manchester', 'Vienna'],
        'Madrid': ['Manchester', 'Vienna'],
    }

    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    remaining_cities = ['Stuttgart', 'Madrid', 'Vienna']

    for perm in itertools.permutations(remaining_cities):
        sequence = ['Manchester'] + list(perm)
        valid = True
        for i in range(3):
            current = sequence[i]
            next_city = sequence[i + 1]
            if next_city not in flights[current]:
                valid = False
                break
        if not valid:
            continue

        T1 = required_durations[sequence[0]]
        T2 = T1 + required_durations[sequence[1]] - 1
        T3 = T2 + required_durations[sequence[2]] - 1
        if 16 - T3 != required_durations[sequence[3]]:
            continue

        if T1 < 1 or T2 < T1 or T3 < T2 or T3 > 15:
            continue

        stuttgart_index = sequence.index('Stuttgart')
        if stuttgart_index == 1:
            stuttgart_start, stuttgart_end = T1, T2
        elif stuttgart_index == 2:
            stuttgart_start, stuttgart_end = T2, T3
        elif stuttgart_index == 3:
            stuttgart_start, stuttgart_end = T3, 15
        else:
            continue

        if not (stuttgart_start <= 15 and stuttgart_end >= 11):
            continue

        itinerary = []
        itinerary.append({'day_range': f'Day 1-{T1}', 'place': sequence[0]})
        itinerary.append({'day_range': f'Day {T1}-{T2}', 'place': sequence[1]})
        itinerary.append({'day_range': f'Day {T2}-{T3}', 'place': sequence[2]})
        itinerary.append({'day_range': f'Day {T3}-15', 'place': sequence[3]})

        print(json.dumps({'itinerary': itinerary}, indent=2))
        return

    print(json.dumps({'error': 'No valid itinerary found'}))

if __name__ == '__main__':
    main()