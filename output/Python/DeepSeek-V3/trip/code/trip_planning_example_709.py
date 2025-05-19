import json
from itertools import permutations

def find_valid_itinerary():
    # Input parameters
    total_days = 18
    city_stays = {
        'Helsinki': 4,
        'Valencia': 5,
        'Dubrovnik': 4,
        'Porto': 3,
        'Prague': 3,
        'Reykjavik': 4
    }
    porto_meet_range = (16, 18)
    
    # Direct flights graph
    direct_flights = {
        'Helsinki': ['Prague', 'Reykjavik', 'Dubrovnik'],
        'Prague': ['Helsinki', 'Valencia', 'Reykjavik'],
        'Valencia': ['Prague', 'Porto'],
        'Porto': ['Valencia'],
        'Reykjavik': ['Helsinki', 'Prague'],
        'Dubrovnik': ['Helsinki']
    }
    
    # Generate all possible permutations of the cities
    cities = list(city_stays.keys())
    
    for perm in permutations(cities):
        # Check if the permutation is a valid path considering direct flights
        valid_path = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in direct_flights[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
        
        # Check if Porto is visited within the meet range
        porto_index = perm.index('Porto')
        days_before_porto = sum(city_stays[city] for city in perm[:porto_index]) + porto_index
        porto_start = days_before_porto + 1
        porto_end = porto_start + city_stays['Porto'] - 1
        
        if not (porto_meet_range[0] <= porto_end <= porto_meet_range[1]):
            continue
        
        # Check total days
        total_trip_days = sum(city_stays.values()) + (len(city_stays) - 1)
        if total_trip_days != total_days:
            continue
        
        # If all conditions are met, construct the itinerary
        itinerary = []
        current_day = 1
        for i, city in enumerate(perm):
            stay_days = city_stays[city]
            end_day = current_day + stay_days - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            if i < len(perm) - 1:
                itinerary.append({
                    'flying': f'Day {end_day}-{end_day}',
                    'from': city,
                    'to': perm[i+1]
                })
                current_day = end_day + 1
        return itinerary
    
    return None

itinerary = find_valid_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))