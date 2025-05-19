import json
from itertools import permutations

def find_valid_itinerary():
    # Cities and their required days
    cities = {
        'Lisbon': 2,
        'Dubrovnik': 5,
        'Copenhagen': 5,
        'Prague': 3,
        'Tallinn': 2,
        'Stockholm': 4,
        'Split': 3,
        'Lyon': 2
    }
    
    # Direct flights
    direct_flights = {
        'Dubrovnik': ['Stockholm', 'Copenhagen'],
        'Lisbon': ['Copenhagen', 'Lyon', 'Stockholm', 'Prague'],
        'Copenhagen': ['Lisbon', 'Stockholm', 'Split', 'Dubrovnik', 'Prague', 'Tallinn'],
        'Prague': ['Stockholm', 'Lyon', 'Lisbon', 'Split', 'Copenhagen'],
        'Tallinn': ['Stockholm', 'Prague', 'Copenhagen'],
        'Stockholm': ['Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Lisbon', 'Split'],
        'Split': ['Copenhagen', 'Stockholm', 'Prague', 'Lyon'],
        'Lyon': ['Lisbon', 'Prague', 'Split']
    }
    
    # Constraints
    constraints = [
        {'city': 'Lisbon', 'day_range': (4, 5)},
        {'city': 'Tallinn', 'day_range': (1, 2)},
        {'city': 'Stockholm', 'day_range': (13, 16)},
        {'city': 'Lyon', 'day_range': (18, 19)}
    ]
    
    # Generate all possible permutations of cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        valid = True
        
        for i, city in enumerate(perm):
            days = cities[city]
            
            # Check if the current city placement satisfies constraints
            for constraint in constraints:
                if constraint['city'] == city:
                    start, end = constraint['day_range']
                    if not (current_day <= start and current_day + days - 1 >= end):
                        valid = False
                        break
            if not valid:
                break
            
            # Add stay
            itinerary.append({
                'day_range': f'Day {current_day}-{current_day + days - 1}',
                'place': city
            })
            
            current_day += days
            
            # Add flight if not last city
            if i < len(perm) - 1:
                next_city = perm[i + 1]
                if next_city not in direct_flights[city]:
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {current_day - 1}-{current_day - 1}',
                    'from': city,
                    'to': next_city
                })
        
        # Check if all days are used and all cities are visited
        if valid and current_day - 1 == 19:
            return itinerary
    
    return None

itinerary = find_valid_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))