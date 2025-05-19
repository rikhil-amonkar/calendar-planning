import json
from itertools import permutations

def find_itinerary():
    # Input parameters
    total_days = 21
    city_stays = {
        'Oslo': 5,
        'Stuttgart': 5,
        'Reykjavik': 2,
        'Split': 3,
        'Geneva': 2,
        'Porto': 3,
        'Tallinn': 5,
        'Stockholm': 3
    }
    
    # Constraints
    constraints = [
        {'place': 'Reykjavik', 'day_range': (1, 2)},
        {'place': 'Porto', 'day_range': (19, 21)},
        {'place': 'Stockholm', 'day_range': (2, 4)}
    ]
    
    # Flight connections
    flights = {
        'Reykjavik': ['Stuttgart', 'Stockholm', 'Tallinn', 'Oslo'],
        'Stockholm': ['Oslo', 'Stuttgart', 'Split', 'Geneva', 'Reykjavik'],
        'Stuttgart': ['Porto', 'Reykjavik', 'Stockholm', 'Split'],
        'Oslo': ['Split', 'Geneva', 'Porto', 'Stockholm', 'Tallinn', 'Reykjavik'],
        'Split': ['Stuttgart', 'Geneva', 'Stockholm', 'Oslo'],
        'Geneva': ['Porto', 'Split', 'Stockholm', 'Oslo'],
        'Tallinn': ['Oslo', 'Reykjavik'],
        'Porto': ['Stuttgart', 'Geneva', 'Oslo']
    }
    
    # Generate all possible city permutations
    cities = list(city_stays.keys())
    for perm in permutations(cities):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if Reykjavik is first
        if perm[0] != 'Reykjavik':
            continue
        
        prev_city = None
        for city in perm:
            if prev_city is not None:
                if city not in flights[prev_city]:
                    valid = False
                    break
                # Add flying day
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 1
            
            # Check constraints
            stay_days = city_stays[city]
            end_day = current_day + stay_days - 1
            
            for constraint in constraints:
                if constraint['place'] == city:
                    const_start, const_end = constraint['day_range']
                    if not (current_day <= const_end and end_day >= const_start):
                        valid = False
                        break
                    # Adjust to fit constraint
                    if current_day > const_start:
                        # Need to move current_day back, but that's not possible
                        valid = False
                        break
                    if end_day < const_end:
                        # Need to extend stay, but days are fixed
                        valid = False
                        break
            
            if not valid:
                break
            
            # Add stay
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            current_day = end_day + 1
            prev_city = city
        
        if valid and current_day - 1 <= total_days:
            # Check if all cities are included
            if len(set(perm)) == len(cities):
                return itinerary
    
    return None

itinerary = find_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))