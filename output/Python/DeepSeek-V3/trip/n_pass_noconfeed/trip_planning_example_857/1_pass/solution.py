import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Porto': {'days': 2, 'constraints': []},
        'Geneva': {'days': 3, 'constraints': []},
        'Mykonos': {'days': 3, 'constraints': [{'start': 10, 'end': 12}]},
        'Manchester': {'days': 4, 'constraints': [{'start': 15, 'end': 18}]},
        'Hamburg': {'days': 5, 'constraints': []},
        'Naples': {'days': 5, 'constraints': []},
        'Frankfurt': {'days': 2, 'constraints': [{'start': 5, 'end': 6}]}
    }
    
    flight_routes = {
        'Hamburg': ['Frankfurt', 'Porto', 'Geneva', 'Manchester'],
        'Frankfurt': ['Hamburg', 'Geneva', 'Porto', 'Naples', 'Manchester'],
        'Porto': ['Hamburg', 'Frankfurt', 'Geneva', 'Manchester'],
        'Geneva': ['Hamburg', 'Frankfurt', 'Porto', 'Mykonos', 'Manchester', 'Naples'],
        'Mykonos': ['Geneva', 'Naples'],
        'Naples': ['Mykonos', 'Frankfurt', 'Geneva', 'Manchester'],
        'Manchester': ['Geneva', 'Naples', 'Frankfurt', 'Porto', 'Hamburg']
    }
    
    city_names = list(cities.keys())
    
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        for i in range(len(perm)):
            city = perm[i]
            days_needed = cities[city]['days']
            
            if i > 0:
                prev_city = perm[i-1]
                if city not in flight_routes[prev_city]:
                    valid = False
                    break
            
            for constraint in cities[city]['constraints']:
                start = constraint['start']
                end = constraint['end']
                if not (current_day <= start and current_day + days_needed - 1 >= end):
                    valid = False
                    break
            if not valid:
                break
            
            day_range = f"Day {current_day}-{current_day + days_needed - 1}"
            itinerary.append({'day_range': day_range, 'place': city})
            current_day += days_needed
        
        if valid and current_day - 1 == 18:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result))