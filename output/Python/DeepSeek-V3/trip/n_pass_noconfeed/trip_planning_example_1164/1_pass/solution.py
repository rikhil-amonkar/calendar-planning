import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Reykjavik': {'duration': 2, 'constraints': [(3, 4)]},
        'Stockholm': {'duration': 2, 'constraints': [(4, 5)]},
        'Porto': {'duration': 5, 'constraints': [(13, 17)]},
        'Nice': {'duration': 3, 'constraints': []},
        'Venice': {'duration': 4, 'constraints': []},
        'Vienna': {'duration': 3, 'constraints': [(11, 13)]},
        'Split': {'duration': 3, 'constraints': []},
        'Copenhagen': {'duration': 2, 'constraints': []}
    }
    
    flight_connections = {
        'Copenhagen': ['Vienna', 'Split', 'Nice', 'Venice', 'Porto', 'Stockholm', 'Reykjavik'],
        'Nice': ['Stockholm', 'Reykjavik', 'Porto', 'Venice', 'Vienna', 'Copenhagen'],
        'Split': ['Copenhagen', 'Stockholm', 'Vienna'],
        'Reykjavik': ['Nice', 'Vienna', 'Copenhagen', 'Stockholm'],
        'Stockholm': ['Nice', 'Copenhagen', 'Split', 'Vienna', 'Reykjavik'],
        'Porto': ['Nice', 'Copenhagen', 'Vienna'],
        'Venice': ['Nice', 'Vienna', 'Copenhagen'],
        'Vienna': ['Copenhagen', 'Nice', 'Reykjavik', 'Stockholm', 'Split', 'Venice', 'Porto']
    }
    
    city_list = list(cities.keys())
    
    for perm in permutations(city_list):
        itinerary = []
        current_day = 1
        valid = True
        
        for i in range(len(perm)):
            city = perm[i]
            duration = cities[city]['duration']
            start_day = current_day
            end_day = current_day + duration - 1
            
            for (min_day, max_day) in cities[city]['constraints']:
                if not (start_day <= max_day and end_day >= min_day):
                    valid = False
                    break
            
            if not valid:
                break
            
            itinerary.append({'city': city, 'start_day': start_day, 'end_day': end_day})
            
            if i < len(perm) - 1:
                next_city = perm[i+1]
                if next_city not in flight_connections[city]:
                    valid = False
                    break
                current_day = end_day + 1
        
        if valid and current_day - 1 <= 17:
            result = {'itinerary': []}
            for entry in itinerary:
                day_range = f"Day {entry['start_day']}-{entry['end_day']}" if entry['start_day'] != entry['end_day'] else f"Day {entry['start_day']}"
                result['itinerary'].append({'day_range': day_range, 'place': entry['city']})
            return result
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))