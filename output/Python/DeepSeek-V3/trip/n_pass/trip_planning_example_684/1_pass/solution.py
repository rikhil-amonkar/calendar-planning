import json
from itertools import permutations

def find_itinerary():
    total_days = 23
    city_stays = {
        'Amsterdam': 4,
        'Edinburgh': 5,
        'Brussels': 5,
        'Vienna': 5,
        'Berlin': 4,
        'Reykjavik': 5
    }
    
    constraints = {
        'Amsterdam': {'day_range': (5, 8)},
        'Berlin': {'day_range': (16, 19)},
        'Reykjavik': {'day_range': (12, 16)}
    }
    
    direct_flights = {
        'Edinburgh': ['Berlin', 'Amsterdam', 'Brussels'],
        'Amsterdam': ['Berlin', 'Edinburgh', 'Reykjavik', 'Vienna'],
        'Vienna': ['Berlin', 'Brussels', 'Reykjavik', 'Amsterdam'],
        'Berlin': ['Edinburgh', 'Amsterdam', 'Vienna', 'Brussels', 'Reykjavik'],
        'Brussels': ['Berlin', 'Edinburgh', 'Vienna', 'Reykjavik'],
        'Reykjavik': ['Vienna', 'Amsterdam', 'Brussels', 'Berlin']
    }
    
    cities = list(city_stays.keys())
    
    for perm in permutations(cities):
        itinerary = []
        current_day = 1
        valid = True
        
        for i in range(len(perm)):
            city = perm[i]
            stay = city_stays[city]
            
            if i < len(perm) - 1:
                next_city = perm[i+1]
                if next_city not in direct_flights[city]:
                    valid = False
                    break
            
            day_range_start = current_day
            day_range_end = current_day + stay - 1
            
            if city in constraints:
                constr_start, constr_end = constraints[city]['day_range']
                if not (day_range_start <= constr_end and day_range_end >= constr_start):
                    valid = False
                    break
            
            itinerary.append({
                'day_range': f"Day {day_range_start}-{day_range_end}",
                'place': city
            })
            current_day += stay
        
        if valid and current_day - 1 == total_days:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))