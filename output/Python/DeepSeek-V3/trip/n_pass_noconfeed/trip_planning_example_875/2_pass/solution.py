import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Stuttgart': {'duration': 3, 'constraints': [(11, 13)]},
        'Edinburgh': {'duration': 4, 'constraints': []},
        'Athens': {'duration': 4, 'constraints': []},
        'Split': {'duration': 2, 'constraints': [(13, 14)]},
        'Krakow': {'duration': 4, 'constraints': [(8, 11)]},
        'Venice': {'duration': 5, 'constraints': []},
        'Mykonos': {'duration': 4, 'constraints': []}
    }
    
    direct_flights = {
        'Krakow': ['Split', 'Edinburgh', 'Stuttgart'],
        'Split': ['Krakow', 'Athens', 'Stuttgart'],
        'Edinburgh': ['Krakow', 'Stuttgart', 'Venice', 'Athens'],
        'Venice': ['Stuttgart', 'Edinburgh', 'Athens'],
        'Stuttgart': ['Venice', 'Krakow', 'Edinburgh', 'Athens', 'Split'],
        'Athens': ['Split', 'Stuttgart', 'Edinburgh', 'Venice', 'Mykonos'],
        'Mykonos': ['Athens']
    }
    
    city_names = list(cities.keys())
    
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        for i in range(len(perm)):
            city = perm[i]
            duration = cities[city]['duration']
            start_day = current_day
            end_day = current_day + duration - 1
            
            # Check if the total days exceed 20
            if end_day > 20:
                valid = False
                break
                
            # Check constraints (must overlap with at least one day of the constraint window)
            if cities[city]['constraints']:
                constraint_satisfied = False
                for (constraint_start, constraint_end) in cities[city]['constraints']:
                    if not (end_day < constraint_start or start_day > constraint_end):
                        constraint_satisfied = True
                        break
                if not constraint_satisfied:
                    valid = False
                    break
            
            # Check flight connections
            if i > 0:
                prev_city = perm[i-1]
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
            
            itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
            current_day = end_day + 1
        
        if valid and current_day - 1 <= 20:
            # Verify all cities are included
            included_cities = {item['place'] for item in itinerary}
            if included_cities == set(city_names):
                return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))