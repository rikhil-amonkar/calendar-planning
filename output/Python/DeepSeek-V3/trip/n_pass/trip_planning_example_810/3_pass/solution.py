import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Berlin': {'duration': 3, 'constraints': [(1, 1), (3, 3)]},
        'Nice': {'duration': 5, 'constraints': []},
        'Athens': {'duration': 5, 'constraints': []},
        'Stockholm': {'duration': 5, 'constraints': []},
        'Barcelona': {'duration': 2, 'constraints': [(3, 4)]},
        'Vilnius': {'duration': 4, 'constraints': []},
        'Lyon': {'duration': 2, 'constraints': [(4, 5)]}
    }
    
    direct_flights = {
        'Lyon': ['Nice', 'Barcelona'],
        'Stockholm': ['Athens', 'Berlin', 'Nice', 'Barcelona'],
        'Nice': ['Lyon', 'Athens', 'Berlin', 'Barcelona', 'Stockholm'],
        'Athens': ['Stockholm', 'Nice', 'Berlin', 'Barcelona', 'Vilnius'],
        'Berlin': ['Athens', 'Nice', 'Barcelona', 'Vilnius', 'Stockholm'],
        'Barcelona': ['Berlin', 'Nice', 'Athens', 'Stockholm', 'Lyon'],
        'Vilnius': ['Berlin', 'Athens']
    }
    
    city_names = list(cities.keys())
    total_days = 20
    
    # We'll try all possible permutations of cities
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        for i, city in enumerate(perm):
            duration = cities[city]['duration']
            start_day = current_day
            end_day = current_day + duration - 1
            
            # Check if this exceeds total days
            if end_day > total_days:
                valid = False
                break
                
            # Check constraints
            for constraint_day, required_day in cities[city]['constraints']:
                if not (start_day <= required_day <= end_day):
                    valid = False
                    break
            if not valid:
                break
            
            # Check flight connections
            if i > 0:
                prev_city = perm[i-1]
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
            
            itinerary.append({'day_range': f"Day {start_day}-{end_day}", 'place': city})
            current_day = end_day + 1
        
        # Check if we exactly filled 20 days and visited all cities
        if valid and current_day == total_days + 1 and len(itinerary) == len(city_names):
            return {'itinerary': itinerary}
    
    # If no permutation worked, try combinations that might not include all cities
    # but sum up to exactly 20 days
    city_combinations = []
    for r in range(1, len(city_names)+1):
        city_combinations.extend(permutations(city_names, r))
    
    for perm in city_combinations:
        itinerary = []
        current_day = 1
        valid = True
        
        for i, city in enumerate(perm):
            duration = cities[city]['duration']
            start_day = current_day
            end_day = current_day + duration - 1
            
            if end_day > total_days:
                valid = False
                break
                
            for constraint_day, required_day in cities[city]['constraints']:
                if not (start_day <= required_day <= end_day):
                    valid = False
                    break
            if not valid:
                break
            
            if i > 0:
                prev_city = perm[i-1]
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
            
            itinerary.append({'day_range': f"Day {start_day}-{end_day}", 'place': city})
            current_day = end_day + 1
        
        if valid and current_day == total_days + 1:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))