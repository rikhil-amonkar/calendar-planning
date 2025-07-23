import json
from itertools import permutations

# Define city_days as a global variable
city_days = {
    'Krakow': 5,
    'Frankfurt': 4,
    'Oslo': 3,
    'Dubrovnik': 5,
    'Naples': 5
}

def find_itinerary():
    total_days = 18
    
    flight_routes = {
        'Dubrovnik': ['Oslo', 'Frankfurt', 'Naples'],
        'Frankfurt': ['Krakow', 'Oslo', 'Dubrovnik'],
        'Krakow': ['Frankfurt', 'Oslo'],
        'Naples': ['Oslo', 'Dubrovnik', 'Frankfurt'],
        'Oslo': ['Dubrovnik', 'Frankfurt', 'Krakow', 'Naples']
    }
    
    def is_valid_sequence(sequence):
        for i in range(len(sequence) - 1):
            if sequence[i+1] not in flight_routes[sequence[i]]:
                return False
        return True
    
    # Generate all possible permutations of cities
    for perm in permutations(city_days.keys()):
        # Skip permutations that don't end with Oslo
        if perm[-1] != 'Oslo':
            continue
            
        if not is_valid_sequence(perm):
            continue
        
        itinerary = []
        current_day = 1
        valid = True
        
        for city in perm:
            days = city_days[city]
            day_end = current_day + days - 1
            
            # Special handling for Oslo (must be days 16-18)
            if city == 'Oslo':
                if current_day != 16:
                    valid = False
                    break
                day_end = 18
            
            # Special handling for Dubrovnik (must include some days between 5-9)
            if city == 'Dubrovnik':
                if not (current_day <= 9 and day_end >= 5):
                    valid = False
                    break
            
            itinerary.append({
                'day_range': f"Day {current_day}-{day_end}",
                'place': city
            })
            
            current_day = day_end + 1
        
        # Check if we used all days and all constraints are satisfied
        if valid and current_day - 1 == total_day:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Use the systematic approach
result = find_itinerary()
print(json.dumps(result, indent=2))