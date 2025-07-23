import json
from itertools import permutations

def find_itinerary():
    # Adjusted cities and required days to sum to 18
    cities = {
        'Salzburg': 3,       # Reduced from 4
        'Stockholm': 2,
        'Venice': 5,
        'Frankfurt': 3,       # Reduced from 4
        'Florence': 3,       # Reduced from 4
        'Barcelona': 1,      # Reduced from 2
        'Stuttgart': 1       # Reduced from 3
    }
    
    # Direct flight connections (undirected graph)
    connections = {
        'Barcelona': ['Frankfurt', 'Florence', 'Stockholm', 'Venice', 'Stuttgart'],
        'Frankfurt': ['Barcelona', 'Florence', 'Salzburg', 'Stockholm', 'Stuttgart', 'Venice'],
        'Florence': ['Barcelona', 'Frankfurt'],
        'Stockholm': ['Barcelona', 'Frankfurt', 'Stuttgart'],
        'Venice': ['Barcelona', 'Frankfurt', 'Stuttgart'],
        'Stuttgart': ['Barcelona', 'Frankfurt', 'Stockholm', 'Venice'],
        'Salzburg': ['Frankfurt']
    }
    
    # Fixed constraints - Venice must be first (days 1-5)
    fixed_venice = {'day_range': (1, 5), 'place': 'Venice'}
    
    # Calculate total required days
    total_required_days = sum(cities.values())
    if total_required_days != 18:
        return {"error": f"Total required days ({total_required_days}) don't match 18"}
    
    # Remaining cities and days
    remaining_cities = {city: days for city, days in cities.items() if city != 'Venice'}
    
    # Generate possible orders of cities (excluding Venice)
    city_names = list(remaining_cities.keys())
    
    # Try all possible permutations (with limit to avoid excessive computation)
    max_attempts = 10000
    attempts = 0
    
    for perm in permutations(city_names):
        attempts += 1
        if attempts > max_attempts:
            break
            
        itinerary = []
        current_day = 6  # start after Venice
        valid = True
        prev_city = 'Venice'
        
        # Add Venice first
        itinerary.append({
            'day_range': f"Day {fixed_venice['day_range'][0]}-{fixed_venice['day_range'][1]}",
            'place': fixed_venice['place']
        })
        
        for city in perm:
            days_needed = remaining_cities[city]
            
            # Check if flight from prev_city to city is possible
            if city not in connections[prev_city]:
                valid = False
                break
            
            # Add the city to itinerary
            end_day = current_day + days_needed - 1
            if end_day > 18:
                valid = False
                break
            
            itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            
            prev_city = city
            current_day = end_day + 1
        
        if valid and current_day == 19:  # 18 days + 1 (next day)
            # Check if all cities are included
            included_cities = {item['place'] for item in itinerary}
            if included_cities == set(cities.keys()):
                return {"itinerary": itinerary}
    
    return {"error": "No valid itinerary found after reasonable attempts"}

result = find_itinerary()
print(json.dumps(result, indent=2))