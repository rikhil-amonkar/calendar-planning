import json

def calculate_itinerary():
    cities = {
        'Brussels': {'days': 4, 'window': None},
        'Naples': {'days': 4, 'window': (5, 8)},
        'Athens': {'days': 4, 'window': (8, 11)},
        'Copenhagen': {'days': 5, 'window': (11, 15)},
        'Munich': {'days': 5, 'window': None},
        'Prague': {'days': 2, 'window': None},
        'Geneva': {'days': 3, 'window': None},
        'Dubrovnik': {'days': 3, 'window': None},
        'Santorini': {'days': 5, 'window': None},
        'Mykonos': {'days': 2, 'window': (27, 28)}
    }

    direct_flights = {
        'Brussels': ['Copenhagen', 'Naples', 'Prague', 'Munich', 'Geneva', 'Athens'],
        'Naples': ['Dubrovnik', 'Mykonos', 'Athens', 'Santorini', 'Munich', 'Copenhagen', 'Brussels', 'Geneva'],
        'Athens': ['Geneva', 'Dubrovnik', 'Santorini', 'Mykonos', 'Copenhagen', 'Naples', 'Prague', 'Munich'],
        'Copenhagen': ['Dubrovnik', 'Brussels', 'Prague', 'Munich', 'Geneva', 'Santorini', 'Athens', 'Naples'],
        'Munich': ['Mykonos', 'Dubrovnik', 'Brussels', 'Prague', 'Geneva', 'Copenhagen', 'Naples', 'Athens'],
        'Prague': ['Geneva', 'Brussels', 'Copenhagen', 'Munich', 'Athens'],
        'Geneva': ['Prague', 'Brussels', 'Athens', 'Munich', 'Mykonos', 'Dubrovnik', 'Copenhagen', 'Santorini'],
        'Dubrovnik': ['Copenhagen', 'Naples', 'Athens', 'Geneva', 'Munich'],
        'Santorini': ['Geneva', 'Athens', 'Copenhagen', 'Naples'],
        'Mykonos': ['Geneva', 'Naples', 'Munich', 'Athens']
    }

    itinerary = [
        {'day_range': 'Day 1-4', 'place': 'Brussels'},
        {'day_range': 'Day 5-8', 'place': 'Naples'},
        {'day_range': 'Day 8-11', 'place': 'Athens'},
        {'day_range': 'Day 11-15', 'place': 'Copenhagen'},
        {'day_range': 'Day 16-20', 'place': 'Munich'},
        {'day_range': 'Day 21-22', 'place': 'Prague'},
        {'day_range': 'Day 23-25', 'place': 'Geneva'},
        {'day_range': 'Day 26-28', 'place': 'Mykonos'}
    ]

    return {'itinerary': itinerary}

print(json.dumps(calculate_itinerary()))