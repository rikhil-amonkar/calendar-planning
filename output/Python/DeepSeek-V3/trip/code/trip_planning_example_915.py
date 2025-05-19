import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        'Bucharest': 3,
        'Venice': 5,
        'Prague': 4,
        'Frankfurt': 5,
        'Zurich': 5,
        'Florence': 5,
        'Tallinn': 5
    }
    
    # Direct flights
    direct_flights = {
        'Prague': ['Tallinn', 'Zurich', 'Florence', 'Bucharest', 'Frankfurt'],
        'Tallinn': ['Prague', 'Frankfurt', 'Zurich'],
        'Zurich': ['Prague', 'Bucharest', 'Frankfurt', 'Florence', 'Venice'],
        'Florence': ['Prague', 'Frankfurt', 'Zurich'],
        'Frankfurt': ['Bucharest', 'Venice', 'Tallinn', 'Zurich', 'Prague', 'Florence'],
        'Bucharest': ['Frankfurt', 'Prague', 'Zurich'],
        'Venice': ['Frankfurt', 'Zurich']
    }
    
    # Constraints
    constraints = [
        {'city': 'Venice', 'day_range': (22, 26)},
        {'city': 'Frankfurt', 'day_range': (12, 16)},
        {'city': 'Tallinn', 'day_range': (8, 12)}
    ]
    
    # Fixed stays
    fixed_stays = {
        'Venice': {'start': 22, 'end': 26},
        'Frankfurt': {'start': 12, 'end': 16},
        'Tallinn': {'start': 8, 'end': 12}
    }
    
    # Other cities to place
    other_cities = [city for city in cities.keys() if city not in fixed_stays]
    
    # Generate possible permutations of other cities
    for perm in permutations(other_cities):
        itinerary = []
        current_day = 1
        valid = True
        
        # Place fixed stays first
        planned = {}
        for city in fixed_stays:
            planned[city] = fixed_stays[city]
        
        # Place other cities in the permutation
        for city in perm:
            if city in planned:
                continue
            duration = cities[city]
            end_day = current_day + duration - 1
            # Check if it overlaps with fixed stays
            overlap = False
            for fixed_city in fixed_stays:
                fixed_start = fixed_stays[fixed_city]['start']
                fixed_end = fixed_stays[fixed_city]['end']
                if not (end_day < fixed_start or current_day > fixed_end):
                    overlap = True
                    break
            if overlap:
                valid = False
                break
            planned[city] = {'start': current_day, 'end': end_day}
            current_day = end_day + 1
        
        if not valid:
            continue
        
        # Check if all cities are placed
        if len(planned) != len(cities):
            continue
        
        # Check if total days is 26
        total_days = max([planned[city]['end'] for city in planned])
        if total_days != 26:
            continue
        
        # Build itinerary with flight connections
        sorted_plan = sorted(planned.items(), key=lambda x: x[1]['start'])
        prev_city = None
        for i, (city, days) in enumerate(sorted_plan):
            if i == 0:
                itinerary.append({
                    'day_range': f'Day {days["start"]}-{days["end"]}',
                    'place': city
                })
            else:
                # Check flight connection
                prev_city = sorted_plan[i-1][0]
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {sorted_plan[i-1][1]["end"]}-{sorted_plan[i-1][1]["end"]}',
                    'from': prev_city,
                    'to': city
                })
                itinerary.append({
                    'day_range': f'Day {days["start"]}-{days["end"]}',
                    'place': city
                })
        
        if valid:
            return itinerary
    
    return None

itinerary = find_itinerary()
print(json.dumps(itinerary, indent=2))