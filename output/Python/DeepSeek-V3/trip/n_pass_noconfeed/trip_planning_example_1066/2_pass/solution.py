import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    # Special constraints
    conference_days = (20, 21)
    stuttgart_friend_days = (1, 4)
    
    # Direct flights
    flights = {
        'Helsinki': ['London', 'Madrid', 'Brussels', 'Split'],
        'Split': ['Madrid', 'Helsinki', 'London', 'Stuttgart'],
        'Madrid': ['Split', 'Helsinki', 'London', 'Mykonos', 'Bucharest', 'Brussels'],
        'London': ['Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Split', 'Mykonos', 'Stuttgart'],
        'Brussels': ['London', 'Bucharest', 'Helsinki', 'Madrid'],
        'Bucharest': ['London', 'Brussels', 'Madrid'],
        'Mykonos': ['Madrid', 'London'],
        'Stuttgart': ['London', 'Split']
    }
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if Madrid is on days 20-21
        madrid_pos = perm.index('Madrid')
        madrid_days = cities['Madrid']
        if not (current_day + sum(cities[city] for city in perm[:madrid_pos]) <= conference_days[0] and 
                current_day + sum(cities[city] for city in perm[:madrid_pos+1]) >= conference_days[1]):
            continue
        
        # Check Stuttgart friend days
        stuttgart_pos = perm.index('Stuttgart')
        stuttgart_start = current_day + sum(cities[city] for city in perm[:stuttgart_pos])
        stuttgart_end = stuttgart_start + cities['Stuttgart'] - 1
        if not (stuttgart_start <= stuttgart_friend_days[1] and stuttgart_end >= stuttgart_friend_days[0]):
            continue
        
        # Check flight connections
        prev_city = None
        for city in perm:
            if prev_city and city not in flights[prev_city]:
                valid = False
                break
            prev_city = city
        
        if not valid:
            continue
        
        # Build itinerary
        prev_city = None
        current_day = 1
        for city in perm:
            days = cities[city]
            end_day = current_day + days - 1
            itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            current_day = end_day + 1
        
        # Check total days
        if current_day - 1 == 21:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Execute and print result
result = find_itinerary()
print(json.dumps(result))