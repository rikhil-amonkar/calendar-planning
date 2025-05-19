import json
from itertools import permutations

def find_valid_itinerary():
    cities = {
        'Reykjavik': {'duration': 5, 'constraints': []},
        'Istanbul': {'duration': 4, 'constraints': [('arrival', 5, 8)]},
        'Edinburgh': {'duration': 5, 'constraints': []},
        'Oslo': {'duration': 2, 'constraints': [('arrival', 8, 9)]},
        'Stuttgart': {'duration': 3, 'constraints': []},
        'Bucharest': {'duration': 5, 'constraints': []}
    }
    
    direct_flights = {
        'Bucharest': ['Oslo', 'Istanbul'],
        'Istanbul': ['Oslo', 'Bucharest', 'Edinburgh', 'Stuttgart'],
        'Reykjavik': ['Stuttgart', 'Oslo'],
        'Stuttgart': ['Reykjavik', 'Edinburgh', 'Istanbul'],
        'Oslo': ['Bucharest', 'Istanbul', 'Reykjavik', 'Edinburgh'],
        'Edinburgh': ['Stuttgart', 'Istanbul', 'Oslo']
    }
    
    total_days = 19
    city_names = list(cities.keys())
    
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        for i in range(len(perm)):
            city = perm[i]
            duration = cities[city]['duration']
            arrival_day = current_day
            departure_day = current_day + duration - 1
            
            if departure_day > total_days:
                valid = False
                break
            
            for constraint_type, start, end in cities[city]['constraints']:
                if constraint_type == 'arrival':
                    if not (start <= arrival_day <= end):
                        valid = False
                        break
            
            if not valid:
                break
            
            itinerary.append((city, arrival_day, departure_day))
            
            if i < len(perm) - 1:
                next_city = perm[i + 1]
                if next_city not in direct_flights[city]:
                    valid = False
                    break
                current_day = departure_day + 1
        
        if valid and len(itinerary) == len(city_names):
            formatted_itinerary = []
            for i, (city, start, end) in enumerate(itinerary):
                formatted_itinerary.append({
                    'day_range': f'Day {start}-{end}',
                    'place': city
                })
                if i < len(itinerary) - 1:
                    next_city = itinerary[i + 1][0]
                    formatted_itinerary.append({
                        'flying': f'Day {end + 1}-{end + 1}',
                        'from': city,
                        'to': next_city
                    })
            return formatted_itinerary
    
    return None

itinerary = find_valid_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps([{"error": "No valid itinerary found"}], indent=2))