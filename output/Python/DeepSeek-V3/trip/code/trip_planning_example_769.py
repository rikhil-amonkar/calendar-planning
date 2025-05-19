import json
from itertools import permutations

def find_valid_itinerary():
    # Cities and their required days
    cities = {
        'Porto': 5,
        'Prague': 4,
        'Reykjavik': 4,
        'Santorini': 2,
        'Amsterdam': 2,
        'Munich': 4
    }
    
    # Direct flights
    direct_flights = {
        'Porto': ['Amsterdam', 'Munich'],
        'Amsterdam': ['Porto', 'Munich', 'Reykjavik', 'Santorini', 'Prague'],
        'Munich': ['Amsterdam', 'Porto', 'Reykjavik', 'Prague'],
        'Reykjavik': ['Amsterdam', 'Munich', 'Prague'],
        'Prague': ['Reykjavik', 'Amsterdam', 'Munich'],
        'Santorini': ['Amsterdam']
    }
    
    # Constraints
    constraints = [
        {'place': 'Reykjavik', 'day_range': (4, 7)},  # Wedding between day 4 and 7 (so must be there day 4-6)
        {'place': 'Amsterdam', 'day_range': (14, 16)},  # Conference day 14 and 15
        {'place': 'Munich', 'day_range': (7, 11)}  # Meet friend between day 7 and 10
    ]
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        valid = True
        temp_cities = cities.copy()
        
        for city in perm:
            days_needed = temp_cities[city]
            
            # Check if the city can be placed in the itinerary
            end_day = current_day + days_needed - 1
            if end_day > 16:
                valid = False
                break
            
            # Check constraints
            for constraint in constraints:
                if constraint['place'] == city:
                    start, end = constraint['day_range']
                    if not (current_day <= start and end_day >= end - 1):
                        valid = False
                        break
            
            if not valid:
                break
            
            # Add to itinerary
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            
            # Move to next city
            current_day = end_day + 1
            if current_day > 16:
                break
            
            # Check if next flight is possible
            next_city_index = perm.index(city) + 1
            if next_city_index < len(perm):
                next_city = perm[next_city_index]
                if next_city not in direct_flights.get(city, []):
                    valid = False
                    break
                
                # Add flight day
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': city,
                    'to': next_city
                })
                current_day += 1
        
        # Check if all cities are placed and all days are filled
        if valid and current_day >= 16 and len(itinerary) > 0:
            # Verify all cities are included
            included_cities = {item['place'] for item in itinerary if 'place' in item}
            if included_cities == set(cities.keys()):
                return itinerary
    
    return None

itinerary = find_valid_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps([{"error": "No valid itinerary found"}], indent=2))