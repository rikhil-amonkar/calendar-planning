import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 20
    cities = {
        'Oslo': {'days': 2, 'constraints': [{'range': (16, 17), 'purpose': 'annual show'}]},
        'Reykjavik': {'days': 5, 'constraints': [{'range': (9, 13), 'purpose': 'meet friend'}]},
        'Stockholm': {'days': 4, 'constraints': []},
        'Munich': {'days': 4, 'constraints': [{'range': (13, 16), 'purpose': 'visit relatives'}]},
        'Frankfurt': {'days': 4, 'constraints': [{'range': (17, 20), 'purpose': 'workshop'}]},
        'Barcelona': {'days': 3, 'constraints': []},
        'Bucharest': {'days': 2, 'constraints': []},
        'Split': {'days': 3, 'constraints': []}
    }
    
    direct_flights = {
        'Reykjavik': ['Munich', 'Oslo', 'Frankfurt', 'Barcelona', 'Stockholm'],
        'Munich': ['Reykjavik', 'Frankfurt', 'Bucharest', 'Oslo', 'Stockholm', 'Split', 'Barcelona'],
        'Frankfurt': ['Munich', 'Oslo', 'Barcelona', 'Reykjavik', 'Bucharest', 'Stockholm', 'Split'],
        'Oslo': ['Split', 'Reykjavik', 'Frankfurt', 'Bucharest', 'Barcelona', 'Stockholm', 'Munich'],
        'Bucharest': ['Munich', 'Barcelona', 'Oslo', 'Frankfurt'],
        'Barcelona': ['Bucharest', 'Frankfurt', 'Reykjavik', 'Stockholm', 'Split', 'Oslo', 'Munich'],
        'Stockholm': ['Barcelona', 'Reykjavik', 'Split', 'Munich', 'Frankfurt', 'Oslo'],
        'Split': ['Oslo', 'Barcelona', 'Stockholm', 'Frankfurt', 'Munich']
    }

    # Generate all possible city orders
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)

    valid_itineraries = []

    for order in possible_orders:
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True

        for city in order:
            if prev_city is not None:
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 1  # Travel day

            days_needed = cities[city]['days']
            end_day = current_day + days_needed - 1

            # Check constraints
            for constraint in cities[city]['constraints']:
                start_constraint, end_constraint = constraint['range']
                if not (current_day <= start_constraint and end_day >= end_constraint):
                    valid = False
                    break
            if not valid:
                break

            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            current_day = end_day + 1
            prev_city = city

        if valid and current_day - 1 <= total_days:
            valid_itineraries.append(itinerary)

    # Select the first valid itinerary (can be optimized further)
    if valid_itineraries:
        output = valid_itineraries[0]
    else:
        output = []

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()