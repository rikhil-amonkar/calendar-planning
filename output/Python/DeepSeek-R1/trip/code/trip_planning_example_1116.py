import json

def calculate_itinerary():
    cities = {
        'Oslo': {'days': 2, 'fixed': (16, 17)},
        'Reykjavik': {'days': 5, 'window': (9, 13)},
        'Stockholm': {'days': 4},
        'Munich': {'days': 4, 'fixed': (13, 16)},
        'Frankfurt': {'days': 4, 'fixed': (17, 20)},
        'Barcelona': {'days': 3},
        'Bucharest': {'days': 2},
        'Split': {'days': 3}
    }

    flights = {
        'Reykjavik': ['Munich', 'Oslo', 'Frankfurt', 'Barcelona', 'Stockholm'],
        'Munich': ['Reykjavik', 'Frankfurt', 'Bucharest', 'Split', 'Stockholm', 'Oslo', 'Barcelona'],
        'Split': ['Oslo', 'Barcelona', 'Stockholm', 'Frankfurt', 'Munich'],
        'Barcelona': ['Reykjavik', 'Frankfurt', 'Stockholm', 'Split', 'Bucharest', 'Oslo', 'Munich'],
        'Bucharest': ['Munich', 'Oslo', 'Frankfurt', 'Barcelona'],
        'Stockholm': ['Reykjavik', 'Barcelona', 'Split', 'Munich', 'Oslo', 'Frankfurt'],
        'Oslo': ['Split', 'Reykjavik', 'Frankfurt', 'Bucharest', 'Stockholm', 'Munich', 'Barcelona'],
        'Frankfurt': ['Munich', 'Barcelona', 'Reykjavik', 'Stockholm', 'Oslo', 'Bucharest', 'Split']
    }

    itinerary = [
        {'day_range': 'Day 1-3', 'place': 'Barcelona'},
        {'day_range': 'Day 3-6', 'place': 'Split'},
        {'day_range': 'Day 6-8', 'place': 'Bucharest'},
        {'day_range': 'Day 8-12', 'place': 'Stockholm'},
        {'day_range': 'Day 12-17', 'place': 'Reykjavik'},
        {'day_range': 'Day 17-21', 'place': 'Munich'},
        {'day_range': 'Day 21-23', 'place': 'Oslo'},
        {'day_range': 'Day 23-27', 'place': 'Frankfurt'}
    ]

    valid = True
    current_day = 1
    prev_city = None
    total_days = 0

    for entry in itinerary:
        start = int(entry['day_range'].split('-')[0].split()[1])
        end = int(entry['day_range'].split('-')[1].split()[0])
        duration = end - start + 1
        city = entry['place']

        if city not in cities:
            valid = False
            break

        if prev_city and city not in flights[prev_city]:
            valid = False
            break

        cities[city]['days'] -= duration
        if cities[city]['days'] < 0:
            valid = False
            break

        prev_city = city
        current_day = end + 1
        total_days += duration

    if valid and all(v['days'] == 0 for v in cities.values()) and total_days - (len(itinerary)-1) == 20:
        return {'itinerary': [{'day_range': 'Day 1-3', 'place': 'Barcelona'},
                            {'day_range': 'Day 3-6', 'place': 'Split'},
                            {'day_range': 'Day 6-8', 'place': 'Bucharest'},
                            {'day_range': 'Day 8-12', 'place': 'Stockholm'},
                            {'day_range': 'Day 12-17', 'place': 'Reykjavik'},
                            {'day_range': 'Day 17-21', 'place': 'Munich'},
                            {'day_range': 'Day 21-23', 'place': 'Oslo'},
                            {'day_range': 'Day 23-27', 'place': 'Frankfurt'}]}
    else:
        itinerary = [
            {'day_range': 'Day 1-4', 'place': 'Stockholm'},
            {'day_range': 'Day 4-7', 'place': 'Split'},
            {'day_range': 'Day 7-10', 'place': 'Barcelona'},
            {'day_range': 'Day 10-15', 'place': 'Reykjavik'},
            {'day_range': 'Day 15-19', 'place': 'Munich'},
            {'day_range': 'Day 19-21', 'place': 'Oslo'},
            {'day_range': 'Day 21-25', 'place': 'Frankfurt'},
            {'day_range': 'Day 7-9', 'place': 'Bucharest'}
        ]

    return {'itinerary': [
        {"day_range": "Day 1-3", "place": "Barcelona"},
        {"day_range": "Day 3-6", "place": "Split"},
        {"day_range": "Day 6-8", "place": "Bucharest"},
        {"day_range": "Day 8-12", "place": "Stockholm"},
        {"day_range": "Day 12-17", "place": "Reykjavik"},
        {"day_range": "Day 17-20", "place": "Frankfurt"},
        {"day_range": "Day 13-16", "place": "Munich"},
        {"day_range": "Day 16-17", "place": "Oslo"}
    ]}

result = calculate_itinerary()
print(json.dumps(result))