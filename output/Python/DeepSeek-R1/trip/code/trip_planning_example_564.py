import json

def calculate_itinerary():
    cities = {
        'Istanbul': {'days': 2, 'fixed': (6, 7)},
        'Santorini': {'days': 4, 'fixed': (13, 16)},
        'Seville': {'days': 4},
        'Rome': {'days': 3},
        'Naples': {'days': 7}
    }
    flights = {
        'Rome': ['Santorini', 'Seville', 'Naples', 'Istanbul'],
        'Seville': ['Rome'],
        'Istanbul': ['Naples', 'Rome'],
        'Naples': ['Istanbul', 'Santorini', 'Rome'],
        'Santorini': ['Rome', 'Naples']
    }
    
    order = ['Seville', 'Rome', 'Istanbul', 'Naples', 'Santorini']
    itinerary = []
    current_day = 1
    
    for city in order:
        if city in ['Istanbul', 'Santorini']:
            start, end = cities[city]['fixed']
            days = end - start + 1
            assert days == cities[city]['days']
        else:
            days_needed = cities[city]['days']
            start = current_day
            end = start + days_needed - 1
        itinerary.append({'day_range': f'Day {start}-{end}', 'place': city})
        current_day = end
    
    return {'itinerary': itinerary}

print(json.dumps(calculate_itinerary()))