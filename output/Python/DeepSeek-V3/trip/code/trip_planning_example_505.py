import json
from itertools import permutations

def find_valid_itinerary():
    # Input parameters
    total_days = 8
    city_stays = {
        'Prague': 4,
        'Stuttgart': 2,
        'Split': 2,
        'Krakow': 2,
        'Florence': 2
    }
    flight_connections = {
        'Stuttgart': ['Split', 'Krakow'],
        'Prague': ['Florence', 'Split', 'Krakow'],
        'Krakow': ['Stuttgart', 'Split', 'Prague'],
        'Split': ['Stuttgart', 'Krakow', 'Prague'],
        'Florence': ['Prague']
    }
    
    # Constraints
    wedding_in_stuttgart_day = (2, 3)  # between day 2 and day 3
    meet_in_split_day = (3, 4)         # between day 3 and day 4
    
    # Generate all possible permutations of the cities
    cities = list(city_stays.keys())
    for perm in permutations(cities):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if Stuttgart is visited at the right time for the wedding
        stuttgart_pos = perm.index('Stuttgart')
        split_pos = perm.index('Split')
        
        # Check if Split comes after Stuttgart for meeting friends
        if split_pos <= stuttgart_pos:
            continue
        
        # Build itinerary
        prev_city = None
        for city in perm:
            stay_days = city_stays[city]
            
            # Check flight connection
            if prev_city is not None:
                if city not in flight_connections[prev_city]:
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
            
            # Add stay
            end_day = current_day + stay_days - 1
            if end_day > total_days:
                valid = False
                break
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            
            # Check Stuttgart wedding constraint
            if city == 'Stuttgart':
                if not (current_day <= wedding_in_stuttgart_day[1] and end_day >= wedding_in_stuttgart_day[0]):
                    valid = False
                    break
            
            # Check Split meeting constraint
            if city == 'Split':
                if not (current_day <= meet_in_split_day[1] and end_day >= meet_in_split_day[0]):
                    valid = False
                    break
            
            current_day = end_day + 1
            prev_city = city
        
        if valid and current_day - 1 == total_days:
            return itinerary
    
    return None

itinerary = find_valid_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))