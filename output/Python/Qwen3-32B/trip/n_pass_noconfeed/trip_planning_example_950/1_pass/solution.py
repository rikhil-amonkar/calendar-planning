import itertools
import json

def main():
    # Define cities and their durations
    cities_data = {
        'Rome': 4,
        'Mykonos': 3,
        'Riga': 3,
        'Munich': 4,
        'Bucharest': 4,
        'Nice': 3,
        'Krakow': 2,
    }

    # Define direct flights (bidirectional)
    flights_list = [
        ('Nice', 'Riga'),
        ('Bucharest', 'Munich'),
        ('Mykonos', 'Munich'),
        ('Riga', 'Bucharest'),
        ('Rome', 'Nice'),
        ('Rome', 'Munich'),
        ('Mykonos', 'Nice'),
        ('Rome', 'Mykonos'),
        ('Munich', 'Krakow'),
        ('Rome', 'Bucharest'),
        ('Nice', 'Munich'),
        ('Riga', 'Munich'),
        ('Rome', 'Riga'),
    ]
    flights = set()
    for a, b in flights_list:
        flights.add((a, b))
        flights.add((b, a))

    # Remaining cities after Rome, Mykonos, before Krakow
    remaining_cities = ['Riga', 'Nice', 'Bucharest', 'Munich']

    # Find valid permutation
    valid_perm = None
    for perm in itertools.permutations(remaining_cities):
        # Check if all transitions are valid
        valid = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in flights:
                valid = False
                break
        if not valid:
            continue

        # Check transition from last city to Krakow
        last_city = perm[-1]
        if (last_city, 'Krakow') not in flights:
            continue

        # Calculate end day
        current_start = 6  # after Mykonos ends on day 6
        end_day = 0
        for city in perm:
            duration = cities_data[city]
            end_day = current_start + duration - 1
            current_start = end_day  # next city starts at this end day

        if end_day == 16:
            valid_perm = perm
            break

    if valid_perm is None:
        raise ValueError("No valid itinerary found.")

    # Build the itinerary
    itinerary = []

    # Rome: day 1-4
    itinerary.append({'day_range': f'Day 1-{1 + cities_data["Rome"] - 1}', 'place': 'Rome'})

    # Mykonos: day 4-6
    itinerary.append({'day_range': 'Day 4-6', 'place': 'Mykonos'})

    # Add the permutation cities
    current_start = 6  # Mykonos ends on 6
    for city in valid_perm:
        duration = cities_data[city]
        end_day = current_start + duration - 1
        day_range = f'Day {current_start}-{end_day}'
        itinerary.append({'day_range': day_range, 'place': city})
        current_start = end_day

    # Krakow: day 16-17
    itinerary.append({'day_range': 'Day 16-17', 'place': 'Krakow'})

    # Output as JSON
    print(json.dumps({'itinerary': itinerary}, indent=2))

if __name__ == '__main__':
    main()