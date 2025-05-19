import json

def calculate_itinerary():
    constraints = {
        'total_days': 20,
        'cities': {
            'Athens': {'days': 6, 'fixed_start': 1, 'fixed_end': 6},
            'Naples': {'days': 5, 'fixed_start': 16, 'fixed_end': 20},
            'Zurich': {'days': 6},
            'Valencia': {'days': 6}
        },
        'direct_flights': {
            'Valencia': ['Naples', 'Athens', 'Zurich'],
            'Athens': ['Naples', 'Zurich'],
            'Zurich': ['Naples', 'Athens', 'Valencia'],
            'Naples': ['Valencia', 'Athens', 'Zurich']
        }
    }

    itinerary = [{'day_range': 'Day 1-6', 'place': 'Athens'}]
    current_day = 6

    # Zurich segment
    zurich_duration = constraints['cities']['Zurich']['days']
    zurich_end = current_day + zurich_duration - 1
    itinerary.append({'day_range': f'Day {current_day}-{zurich_end}', 'place': 'Zurich'})
    current_day = zurich_end

    # Valencia segment
    valencia_duration = constraints['cities']['Valencia']['days']
    valencia_end = current_day + valencia_duration - 1
    itinerary.append({'day_range': f'Day {current_day}-{valencia_end}', 'place': 'Valencia'})
    current_day = valencia_end

    # Naples segment
    naples_start = constraints['cities']['Naples']['fixed_start']
    naples_end = constraints['cities']['Naples']['fixed_end']
    itinerary.append({'day_range': f'Day {naples_start}-{naples_end}', 'place': 'Naples'})

    return {'itinerary': itinerary}

print(json.dumps(calculate_itinerary()))