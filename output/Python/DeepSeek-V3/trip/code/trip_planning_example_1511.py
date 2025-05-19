import json
from itertools import permutations

def main():
    # Input parameters
    cities = {
        'Venice': {'duration': 3},
        'Reykjavik': {'duration': 2},
        'Munich': {'duration': 3, 'fixed': (4, 6)},
        'Santorini': {'duration': 3, 'fixed': (8, 10)},
        'Manchester': {'duration': 3},
        'Porto': {'duration': 3},
        'Bucharest': {'duration': 5},
        'Tallinn': {'duration': 4},
        'Valencia': {'duration': 2, 'fixed': (14, 15)},
        'Vienna': {'duration': 5}
    }

    direct_flights = [
        ('Bucharest', 'Manchester'),
        ('Munich', 'Venice'),
        ('Santorini', 'Manchester'),
        ('Vienna', 'Reykjavik'),
        ('Venice', 'Santorini'),
        ('Munich', 'Porto'),
        ('Valencia', 'Vienna'),
        ('Manchester', 'Vienna'),
        ('Porto', 'Vienna'),
        ('Venice', 'Manchester'),
        ('Santorini', 'Vienna'),
        ('Munich', 'Manchester'),
        ('Munich', 'Reykjavik'),
        ('Bucharest', 'Valencia'),
        ('Venice', 'Vienna'),
        ('Bucharest', 'Vienna'),
        ('Porto', 'Manchester'),
        ('Munich', 'Vienna'),
        ('Valencia', 'Porto'),
        ('Munich', 'Bucharest'),
        ('Tallinn', 'Munich'),
        ('Santorini', 'Bucharest'),
        ('Munich', 'Valencia')
    ]

    # Create flight graph
    flight_graph = {city: set() for city in cities}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)

    # Fixed events
    fixed_events = []
    for city, info in cities.items():
        if 'fixed' in info:
            start, end = info['fixed']
            fixed_events.append((start, end, city))

    # Sort fixed events by start day
    fixed_events.sort()

    # Generate possible sequences that respect fixed events
    remaining_cities = [city for city in cities if 'fixed' not in cities[city]]
    possible_sequences = permutations(remaining_cities)

    best_itinerary = None
    best_days_used = float('inf')

    for sequence in possible_sequences:
        # Build full sequence with fixed events
        full_sequence = []
        seq_ptr = 0
        fixed_ptr = 0
        current_day = 1
        valid = True
        itinerary = []

        while current_day <= 24 and (seq_ptr < len(sequence) or fixed_ptr < len(fixed_events)):
            # Check if next is fixed event
            if fixed_ptr < len(fixed_events):
                next_fixed_start, next_fixed_end, fixed_city = fixed_events[fixed_ptr]
                if current_day >= next_fixed_start:
                    # Must do fixed event now
                    if current_day != next_fixed_start:
                        valid = False
                        break
                    if itinerary:
                        last_city = itinerary[-1]['place'] if 'place' in itinerary[-1] else itinerary[-1]['to']
                        if last_city != fixed_city and (last_city not in flight_graph or fixed_city not in flight_graph[last_city]):
                            valid = False
                            break
                        if last_city != fixed_city:
                            itinerary.append({
                                'flying': f'Day {current_day}-{current_day}',
                                'from': last_city,
                                'to': fixed_city
                            })
                    itinerary.append({
                        'day_range': f'Day {next_fixed_start}-{next_fixed_end}',
                        'place': fixed_city
                    })
                    current_day = next_fixed_end + 1
                    fixed_ptr += 1
                    continue

            # Do next in sequence
            if seq_ptr < len(sequence):
                next_city = sequence[seq_ptr]
                duration = cities[next_city]['duration']
                if itinerary:
                    last_city = itinerary[-1]['place'] if 'place' in itinerary[-1] else itinerary[-1]['to']
                    if last_city != next_city and (last_city not in flight_graph or next_city not in flight_graph[last_city]):
                        valid = False
                        break
                    if last_city != next_city:
                        itinerary.append({
                            'flying': f'Day {current_day}-{current_day}',
                            'from': last_city,
                            'to': next_city
                        })
                        current_day += 1
                        if current_day > 24:
                            valid = False
                            break
                itinerary.append({
                    'day_range': f'Day {current_day}-{current_day + duration - 1}',
                    'place': next_city
                })
                current_day += duration
                seq_ptr += 1
            else:
                break

        if not valid:
            continue

        # Check if all cities are visited
        visited_cities = set()
        for item in itinerary:
            if 'place' in item:
                visited_cities.add(item['place'])
            elif 'to' in item:
                visited_cities.add(item['to'])

        if len(visited_cities) == len(cities) and current_day <= 25:
            days_used = current_day - 1
            if days_used < best_days_used:
                best_days_used = days_used
                best_itinerary = itinerary

    # Output the best itinerary found
    if best_itinerary:
        print(json.dumps(best_itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()