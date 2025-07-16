import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Venice': 4,
        'Barcelona': 3,
        'Copenhagen': 4,
        'Lyon': 4,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 2,
        'Tallinn': 5,
        'Munich': 3
    }
    
    constraints = {
        'Barcelona': {'day_range': (10, 12)},
        'Copenhagen': {'day_range': (7, 10)},
        'Dubrovnik': {'day_range': (16, 20)}
    }
    
    direct_flights = {
        'Copenhagen': ['Athens', 'Dubrovnik', 'Munich', 'Reykjavik', 'Barcelona', 'Tallinn', 'Venice'],
        'Munich': ['Tallinn', 'Copenhagen', 'Venice', 'Reykjavik', 'Athens', 'Lyon', 'Dubrovnik', 'Barcelona'],
        'Venice': ['Munich', 'Athens', 'Copenhagen', 'Barcelona', 'Lyon'],
        'Reykjavik': ['Athens', 'Munich', 'Barcelona', 'Copenhagen'],
        'Athens': ['Copenhagen', 'Dubrovnik', 'Venice', 'Reykjavik', 'Munich', 'Barcelona'],
        'Lyon': ['Barcelona', 'Munich', 'Venice'],
        'Barcelona': ['Lyon', 'Dubrovnik', 'Athens', 'Reykjavik', 'Copenhagen', 'Venice', 'Munich', 'Tallinn'],
        'Dubrovnik': ['Copenhagen', 'Athens', 'Barcelona', 'Munich'],
        'Tallinn': ['Munich', 'Barcelona', 'Copenhagen']
    }
    
    city_list = list(cities.keys())
    
    for perm in permutations(city_list):
        itinerary = []
        current_day = 1
        valid = True
        
        for i, city in enumerate(perm):
            duration = cities[city]
            day_range = (current_day, current_day + duration - 1)
            itinerary.append({'day_range': f"Day {day_range[0]}-{day_range[1]}", 'place': city})
            
            if city in constraints:
                constr_range = constraints[city]['day_range']
                if not (day_range[0] <= constr_range[1] and day_range[1] >= constr_range[0]):
                    valid = False
                    break
            
            current_day += duration
            
            if i < len(perm) - 1:
                next_city = perm[i + 1]
                if next_city not in direct_flights.get(city, []):
                    valid = False
                    break
        
        if valid and current_day - 1 == 26:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))