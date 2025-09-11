import itertools
import json

def main():
    # Define allowed direct flights between cities
    allowed_flights = {
        'Nice': ['Dublin', 'Lyon', 'Frankfurt'],
        'Dublin': ['Nice', 'Frankfurt', 'Krakow', 'Lyon'],
        'Krakow': ['Dublin', 'Frankfurt'],
        'Lyon': ['Frankfurt', 'Dublin', 'Nice'],
        'Frankfurt': ['Nice', 'Lyon', 'Dublin', 'Krakow']
    }

    # Define city durations and constraints
    city_durations = {
        'Nice': 5,
        'Krakow': 6,
        'Dublin': 7,
        'Lyon': 4,
        'Frankfurt': 2
    }

    # Fixed cities and their day ranges
    fixed = {
        'Nice': {'start': 1, 'end': 5},
        'Frankfurt': {'start': 19, 'end': 20}
    }

    # Middle cities to arrange between Nice and Frankfurt
    middle_cities = ['Lyon', 'Dublin', 'Krakow']

    # Find valid permutation of middle cities
    valid_order = None
    for perm in itertools.permutations(middle_cities):
        current = 'Nice'
        valid = True
        for city in perm:
            if city not in allowed_flights[current]:
                valid = False
                break
            current = city
        # Check transition to Frankfurt
        if valid and 'Frankfurt' not in allowed_flights[current]:
            valid = False
        if valid:
            valid_order = perm
            break

    if valid_order is None:
        print("No valid itinerary found.")
        return

    # Compute day ranges for each city in the valid order
    itinerary = []
    # Add Nice
    nice_start = fixed['Nice']['start']
    nice_end = fixed['Nice']['end']
    itinerary.append({'day_range': f'Day {nice_start}-{nice_end}', 'place': 'Nice'})

    current_start = nice_end  # Start of next city is end of Nice

    for city in valid_order:
        days = city_durations[city]
        end_day = current_start + days - 1
        day_range = f'Day {current_start}-{end_day}'
        itinerary.append({'day_range': day_range, 'place': city})
        current_start = end_day

    # Add Frankfurt
    frank_start = fixed['Frankfurt']['start']
    frank_end = fixed['Frankfurt']['end']
    itinerary.append({'day_range': f'Day {frank_start}-{frank_end}', 'place': 'Frankfurt'})

    # Output as JSON
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()