import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Dublin': {'duration': 3, 'constraints': [{'range': (7, 9), 'purpose': 'tour'}]},
        'Madrid': {'duration': 2, 'constraints': [{'range': (2, 3), 'purpose': 'relatives'}]},
        'Oslo': {'duration': 3, 'constraints': []},
        'London': {'duration': 2, 'constraints': []},
        'Vilnius': {'duration': 3, 'constraints': []},
        'Berlin': {'duration': 5, 'constraints': [{'range': (3, 7), 'purpose': 'wedding'}]}
    }
    
    direct_flights = {
        'London': ['Madrid', 'Oslo', 'Berlin', 'Dublin'],
        'Madrid': ['London', 'Oslo', 'Berlin', 'Dublin'],
        'Oslo': ['London', 'Madrid', 'Vilnius', 'Berlin', 'Dublin'],
        'Berlin': ['London', 'Madrid', 'Oslo', 'Vilnius', 'Dublin'],
        'Dublin': ['London', 'Madrid', 'Oslo', 'Berlin'],
        'Vilnius': ['Oslo', 'Berlin']
    }
    
    total_days = 13
    city_names = list(cities.keys())
    
    def is_valid_path(path):
        day = 1
        itinerary = []
        remaining_days = {city: cities[city]['duration'] for city in cities}
        
        for i in range(len(path)):
            city = path[i]
            if i > 0:
                prev_city = path[i-1]
                if city not in direct_flights[prev_city]:
                    return False
            
            duration = remaining_days[city]
            start_day = day
            end_day = day + duration - 1
            itinerary.append((start_day, end_day, city))
            day = end_day + 1
        
        # Check if exactly 13 days are used
        if day - 1 != total_days:
            return False
        
        # Check constraints
        for entry in itinerary:
            start, end, city = entry
            for constraint in cities[city]['constraints']:
                c_start, c_end = constraint['range']
                if not (start <= c_end and end >= c_start):
                    return False
        
        return True
    
    def generate_itinerary(path):
        day = 1
        itinerary = []
        remaining_days = {city: cities[city]['duration'] for city in cities}
        
        for i in range(len(path)):
            city = path[i]
            duration = remaining_days[city]
            start_day = day
            end_day = day + duration - 1
            itinerary.append((start_day, end_day, city))
            day = end_day + 1
        
        return itinerary
    
    # Try all permutations (since 6! is manageable)
    for perm in permutations(city_names):
        if is_valid_path(perm):
            itinerary = generate_itinerary(perm)
            result = {'itinerary': []}
            for entry in itinerary:
                start, end, city = entry
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                result['itinerary'].append({'day_range': day_range, 'place': city})
            return result
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))