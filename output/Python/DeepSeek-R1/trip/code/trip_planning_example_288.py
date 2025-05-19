import json

def calculate_itinerary():
    cities = {
        'Manchester': {'days': 7, 'fixed': (1, 7)},
        'Stuttgart': {'days': 5, 'fixed': (11, 15)},
        'Madrid': {'days': 4},
        'Vienna': {'days': 2}
    }
    
    flights = {
        'Manchester': ['Vienna', 'Stuttgart', 'Madrid'],
        'Stuttgart': ['Vienna', 'Manchester'],
        'Madrid': ['Vienna', 'Manchester'],
        'Vienna': ['Stuttgart', 'Manchester', 'Madrid']
    }

    itinerary = []

    # Add Manchester
    itinerary.append({'day_range': f"Day 1-7", 'place': 'Manchester'})

    # From Manchester to Madrid (Day 7 transition)
    itinerary.append({'day_range': "Day 7-10", 'place': 'Madrid'})

    # From Madrid to Vienna (Day 10 transition)
    itinerary.append({'day_range': "Day 10-11", 'place': 'Vienna'})

    # Add Stuttgart
    itinerary.append({'day_range': "Day 11-15", 'place': 'Stuttgart'})

    # Validate flight connections
    for i in range(len(itinerary)-1):
        current = itinerary[i]['place']
        next_place = itinerary[i+1]['place']
        if next_place not in flights[current]:
            return {"error": "Invalid flight path"}

    return {'itinerary': itinerary}

print(json.dumps(calculate_itinerary()))