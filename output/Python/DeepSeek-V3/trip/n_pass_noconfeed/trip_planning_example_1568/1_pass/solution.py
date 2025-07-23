import json
from itertools import permutations

def main():
    # Define cities and their required days
    cities = {
        'Prague': {'total_days': 5, 'fixed': (5, 9)},
        'Brussels': {'total_days': 2},
        'Riga': {'total_days': 2, 'fixed': (15, 16)},
        'Munich': {'total_days': 2},
        'Seville': {'total_days': 3},
        'Stockholm': {'total_days': 2, 'fixed': (16, 17)},
        'Istanbul': {'total_days': 2},
        'Amsterdam': {'total_days': 3},
        'Vienna': {'total_days': 5, 'fixed': (1, 5)},
        'Split': {'total_days': 3, 'fixed': (11, 13)}
    }

    # Define direct flights as a graph
    graph = {
        'Riga': ['Stockholm', 'Munich', 'Brussels', 'Prague', 'Amsterdam', 'Vienna'],
        'Stockholm': ['Riga', 'Brussels', 'Istanbul', 'Amsterdam', 'Vienna', 'Prague', 'Munich', 'Split'],
        'Brussels': ['Stockholm', 'Vienna', 'Prague', 'Munich', 'Istanbul', 'Riga', 'Seville'],
        'Istanbul': ['Munich', 'Riga', 'Stockholm', 'Amsterdam', 'Brussels', 'Prague', 'Vienna'],
        'Prague': ['Split', 'Munich', 'Amsterdam', 'Brussels', 'Istanbul', 'Riga', 'Vienna', 'Stockholm'],
        'Munich': ['Istanbul', 'Amsterdam', 'Brussels', 'Split', 'Stockholm', 'Seville', 'Prague', 'Riga', 'Vienna'],
        'Seville': ['Brussels', 'Amsterdam', 'Vienna', 'Munich'],
        'Amsterdam': ['Munich', 'Split', 'Stockholm', 'Riga', 'Istanbul', 'Vienna', 'Prague', 'Seville'],
        'Vienna': ['Brussels', 'Riga', 'Istanbul', 'Seville', 'Stockholm', 'Split', 'Munich', 'Amsterdam', 'Prague'],
        'Split': ['Prague', 'Munich', 'Stockholm', 'Amsterdam', 'Vienna']
    }

    # Fixed events
    fixed_events = {
        'Prague': (5, 9),
        'Riga': (15, 16),
        'Stockholm': (16, 17),
        'Vienna': (1, 5),
        'Split': (11, 13)
    }

    # Initialize itinerary with fixed events
    itinerary = [None] * 20  # 1-based to 20

    # Assign fixed events
    for city, (start, end) in fixed_events.items():
        for day in range(start, end + 1):
            itinerary[day - 1] = city

    # Assign remaining days for cities with fixed events
    remaining_cities = {}
    for city in cities:
        if 'fixed' in cities[city]:
            fixed_days = cities[city]['fixed'][1] - cities[city]['fixed'][0] + 1
            remaining = cities[city]['total_days'] - fixed_days
            if remaining > 0:
                remaining_cities[city] = remaining
        else:
            remaining_cities[city] = cities[city]['total_days']

    # List of cities to assign (excluding fixed days)
    cities_to_assign = list(remaining_cities.keys())

    # Try permutations to find a valid itinerary
    for perm in permutations(cities_to_assign):
        temp_itinerary = itinerary.copy()
        remaining_days = remaining_cities.copy()
        current_city = None

        # Assign initial city (Vienna)
        current_city = 'Vienna'

        for day in range(20):
            if temp_itinerary[day] is not None:
                current_city = temp_itinerary[day]
                continue

            # Try to stay in current city if remaining days
            if remaining_days.get(current_city, 0) > 0:
                temp_itinerary[day] = current_city
                remaining_days[current_city] -= 1
                continue

            # Try to move to another city
            moved = False
            for next_city in perm:
                if remaining_days.get(next_city, 0) > 0 and next_city in graph[current_city]:
                    temp_itinerary[day] = next_city
                    remaining_days[next_city] -= 1
                    current_city = next_city
                    moved = True
                    break

            if not moved:
                break

        # Check if all days assigned and all cities' days satisfied
        if None not in temp_itinerary and all(v == 0 for v in remaining_days.values()):
            # Convert to day ranges
            day_ranges = []
            current_place = temp_itinerary[0]
            start_day = 1
            for day in range(1, 20):
                if temp_itinerary[day] != current_place:
                    day_ranges.append({
                        'day_range': f'Day {start_day}-{day}',
                        'place': current_place
                    })
                    current_place = temp_itinerary[day]
                    start_day = day + 1
            day_ranges.append({
                'day_range': f'Day {start_day}-20',
                'place': current_place
            })

            print(json.dumps({'itinerary': day_ranges}))
            return

    print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()