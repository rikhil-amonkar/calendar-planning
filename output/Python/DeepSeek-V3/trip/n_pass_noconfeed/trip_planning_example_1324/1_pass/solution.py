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
        'Reykjavik': ['Athens', 'Copenhagen', 'Munich', 'Barcelona'],
        'Athens': ['Copenhagen', 'Dubrovnik', 'Venice', 'Reykjavik', 'Munich', 'Barcelona'],
        'Lyon': ['Barcelona', 'Munich', 'Venice'],
        'Barcelona': ['Lyon', 'Dubrovnik', 'Athens', 'Reykjavik', 'Copenhagen', 'Venice', 'Munich', 'Tallinn'],
        'Dubrovnik': ['Copenhagen', 'Athens', 'Barcelona', 'Munich'],
        'Tallinn': ['Munich', 'Copenhagen', 'Barcelona']
    }
    
    city_list = list(cities.keys())
    
    for perm in permutations(city_list):
        itinerary = []
        current_day = 1
        valid = True
        
        for i in range(len(perm)):
            city = perm[i]
            duration = cities[city]
            
            if i > 0:
                prev_city = perm[i-1]
                if city not in direct_flights.get(prev_city, []):
                    valid = False
                    break
            
            day_range = (current_day, current_day + duration - 1)
            itinerary.append({'day_range': f"Day {day_range[0]}-{day_range[1]}", 'place': city})
            current_day += duration
        
        if not valid or current_day - 1 != 26:
            continue
        
        meets_constraints = True
        for entry in itinerary:
            city = entry['place']
            day_start = int(entry['day_range'].split('-')[0].split(' ')[1])
            day_end = int(entry['day_range'].split('-')[1])
            
            if city in constraints:
                constr_range = constraints[city]['day_range']
                if not (day_start <= constr_range[1] and day_end >= constr_range[0]):
                    meets_constraints = False
                    break
        
        if meets_constraints:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))