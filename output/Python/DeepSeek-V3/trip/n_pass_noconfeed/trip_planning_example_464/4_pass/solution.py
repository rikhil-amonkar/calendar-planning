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
    
    constraints = {
        'Oslo': {'day_range': (16, 18)},  # Oslo must be visited on days 16-18
        'Dubrovnik': {'day_range': (5, 9)}  # Dubrovnik must be visited on days 5-9
    }
    
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
    
    def satisfies_constraints(itinerary):
        for item in itinerary:
            city = item['place']
            if city in constraints:
                start_day = int(item['day_range'].split('-')[0].split()[1])
                end_day = int(item['day_range'].split('-')[1])
                constr_start, constr_end = constraints[city]['day_range']
                if city == 'Oslo':
                    if start_day != 16 or end_day != 18:
                        return False
                elif city == 'Dubrovnik':
                    if not (start_day <= 9 and end_day >= 5):
                        return False
        return True
    
    # Generate all possible permutations of cities
    for perm in permutations(cities):
        # Skip permutations that don't end with Oslo
        if perm[-1] != 'Oslo':
            continue
            
        if not is_valid_sequence(perm):
            continue
        
        itinerary = []
        current_day = 1
        
        for city in perm:
            days = city_days[city]
            day_end = current_day + days - 1
            
            if city == 'Oslo':
                # Force Oslo to be exactly days 16-18
                if day_end != 18:
                    break
                current_day = 16
                day_end = 18
            
            itinerary.append({
                'day_range': f"Day {current_day}-{day_end}",
                'place': city
            })
            current_day = day_end + 1
        
        # Check if we used all days and Dubrovnik is in days 5-9
        if current_day - 1 == total_days:
            # Verify Dubrovnik constraint
            for item in itinerary:
                if item['place'] == 'Dubrovnik':
                    start_day = int(item['day_range'].split('-')[0].split()[1])
                    end_day = int(item['day_range'].split('-')[1])
                    if not (start_day <= 9 and end_day >= 5):
                        break
            else:  # Only if Dubrovnik constraint is satisfied
                if satisfies_constraints(itinerary):
                    return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Define cities list
cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']

# Use the systematic approach
result = find_itinerary()
print(json.dumps(result, indent=2))