import itertools
import json

def main():
    # Define cities and durations
    cities = ['Helsinki', 'Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Madrid', 'Split', 'London']
    durations = {
        'Helsinki': 5,
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Split': 3,
        'London': 5,
    }

    # Direct flights as set of frozensets
    direct_flights = {
        frozenset(['Helsinki', 'London']),
        frozenset(['Split', 'Madrid']),
        frozenset(['Helsinki', 'Madrid']),
        frozenset(['London', 'Madrid']),
        frozenset(['Brussels', 'London']),
        frozenset(['Bucharest', 'London']),
        frozenset(['Brussels', 'Bucharest']),
        frozenset(['Bucharest', 'Madrid']),
        frozenset(['Split', 'Helsinki']),
        frozenset(['Mykonos', 'Madrid']),
        frozenset(['Stuttgart', 'London']),
        frozenset(['Helsinki', 'Brussels']),
        frozenset(['Brussels', 'Madrid']),
        frozenset(['Split', 'London']),
        frozenset(['Stuttgart', 'Split']),
        frozenset(['London', 'Mykonos']),
    }

    # Cities except Madrid
    cities_except_madrid = ['Helsinki', 'Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Split', 'London']

    # Find valid permutations
    for perm in itertools.permutations(cities_except_madrid):
        # Check if the last city in the permutation has a direct flight to Madrid
        last_city = perm[-1]
        if frozenset([last_city, 'Madrid']) not in direct_flights:
            continue

        # Check consecutive cities in the permutation have direct flights
        valid = True
        for i in range(len(perm) - 1):
            city_a = perm[i]
            city_b = perm[i + 1]
            if frozenset([city_a, city_b]) not in direct_flights:
                valid = False
                break
        if not valid:
            continue

        # Check if Stuttgart is in first or second position and start day is <=4
        if 'Stuttgart' not in perm:
            continue  # should not happen as per problem constraints
        stuttgart_index = perm.index('Stuttgart')
        if stuttgart_index not in [0, 1]:
            continue
        # Check start day of Stuttgart
        if stuttgart_index == 0:
            start_day_st = 1
        else:  # stuttgart_index == 1
            first_city = perm[0]
            start_day_st = 1 + durations[first_city]
        if start_day_st > 4:
            continue

        # Found a valid permutation. Now append Madrid and compute day ranges.
        full_itinerary = list(perm) + ['Madrid']

        # Compute day ranges
        itinerary = []
        current_day = 1  # start_day for first city
        for city in full_itinerary:
            duration = durations[city]
            end_day = current_day + duration - 1
            itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            current_day = end_day  # next city starts on this day

        # Now, output the JSON
        output = {'itinerary': itinerary}
        print(json.dumps(output, indent=2))
        return

    # If no solution found
    print(json.dumps({'error': 'No valid itinerary found'}))

if __name__ == '__main__':
    main()