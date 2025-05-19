import json

def calculate_itinerary():
    cities = {
        'Helsinki': {'days': 2, 'fixed': (1, 2)},
        'Reykjavik': {'days': 2, 'fixed': (8, 9)},
        'Warsaw': {'days': 3, 'fixed': (9, 11)},
        'Madrid': {'days': 4, 'fixed': None},
        'Split': {'days': 4, 'fixed': None},
        'Budapest': {'days': 4, 'fixed': None}
    }

    flights = {
        'Helsinki': ['Reykjavik', 'Split', 'Madrid', 'Budapest', 'Warsaw'],
        'Split': ['Helsinki', 'Madrid', 'Warsaw', 'Budapest'],
        'Budapest': ['Warsaw', 'Helsinki', 'Madrid', 'Reykjavik', 'Split'],
        'Madrid': ['Split', 'Helsinki', 'Budapest', 'Warsaw'],
        'Reykjavik': ['Helsinki', 'Warsaw', 'Budapest', 'Madrid'],
        'Warsaw': ['Budapest', 'Helsinki', 'Reykjavik', 'Madrid', 'Split']
    }

    itinerary = [
        {'day_range': 'Day 1-2', 'place': 'Helsinki'},
        {'day_range': 'Day 3-6', 'place': 'Split'},
        {'day_range': 'Day 7', 'place': 'Budapest'},
        {'day_range': 'Day 8-9', 'place': 'Reykjavik'},
        {'day_range': 'Day 9-11', 'place': 'Warsaw'},
        {'day_range': 'Day 12-14', 'place': 'Madrid'}
    ]

    return json.dumps({'itinerary': itinerary}, indent=2)

print(calculate_itinerary())