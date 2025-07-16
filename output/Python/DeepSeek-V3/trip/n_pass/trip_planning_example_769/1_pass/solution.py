import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Porto': {'duration': 5, 'constraints': []},
        'Prague': {'duration': 4, 'constraints': []},
        'Reykjavik': {'duration': 4, 'constraints': [(4, 7)]},
        'Santorini': {'duration': 2, 'constraints': []},
        'Amsterdam': {'duration': 2, 'constraints': [(14, 15)]},
        'Munich': {'duration': 4, 'constraints': [(7, 10)]}
    }
    
    direct_flights = {
        'Porto': ['Amsterdam', 'Munich'],
        'Munich': ['Amsterdam', 'Porto', 'Reykjavik', 'Prague'],
        'Reykjavik': ['Amsterdam', 'Munich', 'Prague'],
        'Amsterdam': ['Porto', 'Munich', 'Reykjavik', 'Prague', 'Santorini'],
        'Prague': ['Reykjavik', 'Amsterdam', 'Munich'],
        'Santorini': ['Amsterdam']
    }
    
    total_days = 16
    city_names = list(cities.keys())
    
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        for i, city in enumerate(perm):
            prev_city = perm[i-1] if i > 0 else None
            duration = cities[city]['duration']
            
            if prev_city and city not in direct_flights[prev_city]:
                valid = False
                break
            
            day_range = f"Day {current_day}-{current_day + duration - 1}"
            itinerary.append({'day_range': day_range, 'place': city})
            current_day += duration
            
            if current_day > total_days + 1:
                valid = False
                break
        
        if not valid or current_day != total_days + 1:
            continue
        
        # Check constraints
        meets_constraints = True
        for entry in itinerary:
            place = entry['place']
            start_day = int(entry['day_range'].split('-')[0].split(' ')[1])
            end_day = int(entry['day_range'].split('-')[1])
            
            for (constraint_start, constraint_end) in cities[place]['constraints']:
                if not (start_day <= constraint_start and end_day >= constraint_end):
                    meets_constraints = False
                    break
            if not meets_constraints:
                break
        
        if meets_constraints:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))