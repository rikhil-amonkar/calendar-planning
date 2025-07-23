import json
from itertools import permutations

def find_itinerary():
    total_days = 18
    city_days = {
        'Krakow': 5,
        'Frankfurt': 4,
        'Oslo': 3,
        'Dubrovnik': 5,
        'Naples': 5
    }
    
    constraints = {
        'Oslo': {'day_range': (16, 18)},
        'Dubrovnik': {'day_range': (5, 9)}
    }
    
    cities = list(city_days.keys())
    flight_routes = {
        'Dubrovnik': ['Oslo', 'Frankfurt', 'Naples'],
        'Frankfurt': ['Krakow', 'Oslo', 'Dubrovnik'],
        'Krakow': ['Frankfurt', 'Oslo'],
        'Naples': ['Oslo', 'Dubrovnik', 'Frankfurt'],
        'Oslo': ['Dubrovnik', 'Frankfurt', 'Krakow', 'Naples']
    }
    
    def is_valid_sequence(sequence):
        for i in range(len(sequence) - 1):
            if sequence[i+1] not in flight_routes[sequence[i]]:
                return False
        return True
    
    for perm in permutations(cities):
        if not is_valid_sequence(perm):
            continue
        
        itinerary = []
        remaining_days = total_days
        current_day = 1
        
        for city in perm:
            days = city_days[city]
            day_end = current_day + days - 1
            
            if city in constraints:
                constr_range = constraints[city]['day_range']
                if not (current_day <= constr_range[1] and day_end >= constr_range[0]):
                    continue
            
            itinerary.append({
                'day_range': f"Day {current_day}-{day_end}",
                'place': city
            })
            current_day = day_end + 1
        
        if current_day - 1 == total_days:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))