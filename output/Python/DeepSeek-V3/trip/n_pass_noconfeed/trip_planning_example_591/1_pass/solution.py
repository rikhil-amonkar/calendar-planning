import json
from itertools import permutations

def find_valid_itinerary():
    # Define the constraints
    total_days = 17
    city_stays = {
        'Stuttgart': 2,
        'Bucharest': 2,
        'Geneva': 4,
        'Valencia': 6,
        'Munich': 7
    }
    geneva_constraint = (1, 4)
    munich_constraint = (4, 10)
    
    # Define the flight connections
    connections = {
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Bucharest': ['Valencia', 'Munich'],
        'Stuttgart': ['Valencia']
    }
    
    # Correcting the city names in connections to match the constraints
    # Note: 'Geneva' is spelled as 'Geneva' in constraints but 'Geneva' in connections
    # Assuming 'Geneva' is correct and 'Geneva' is a typo in connections
    connections['Geneva'] = connections.pop('Geneva', ['Munich', 'Valencia'])
    connections['Munich'] = connections.pop('Munich', ['Geneva', 'Valencia', 'Bucharest'])
    connections['Munich'] = connections.get('Munich', ['Geneva', 'Valencia', 'Bucharest'])
    
    # Generate all possible permutations of the cities
    cities = list(city_stays.keys())
    
    for perm in permutations(cities):
        # Check if the permutation is a valid path considering flight connections
        valid_path = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in connections.get(perm[i], []):
                valid_path = False
                break
        if not valid_path:
            continue
        
        # Try to assign days to the cities in this order
        itinerary = []
        remaining_days = total_days
        current_day = 1
        
        # Assign Geneva first to meet its constraint
        if 'Geneva' in perm:
            geneva_pos = perm.index('Geneva')
            # We need to assign Geneva between day 1 and 4
            # So Geneva must be first or early in the itinerary
            if geneva_pos != 0:
                continue  # Skip if Geneva is not first
            
            geneva_days = city_stays['Geneva']
            if current_day + geneva_days - 1 > geneva_constraint[1]:
                continue  # Doesn't meet Geneva constraint
            
            itinerary.append({
                'day_range': f"Day {current_day}-{current_day + geneva_days - 1}",
                'place': 'Geneva'
            })
            current_day += geneva_days
            remaining_days -= geneva_days
        
        # Now assign Munich to meet its constraint
        if 'Munich' in perm:
            munich_pos = perm.index('Munich')
            # Munich must be after Geneva if Geneva is first
            if 'Geneva' in perm and munich_pos < perm.index('Geneva'):
                continue
            
            munich_days = city_stays['Munich']
            # Check if Munich can be assigned between day 4 and 10
            if current_day > munich_constraint[1] or current_day + munich_days - 1 < munich_constraint[0]:
                continue
            
            itinerary.append({
                'day_range': f"Day {current_day}-{current_day + munich_days - 1}",
                'place': 'Munich'
            })
            current_day += munich_days
            remaining_days -= munich_days
        
        # Assign remaining cities
        for city in perm:
            if city in ['Geneva', 'Munich']:
                continue
            
            city_days = city_stays[city]
            if remaining_days < city_days:
                valid_path = False
                break
            
            itinerary.append({
                'day_range': f"Day {current_day}-{current_day + city_days - 1}",
                'place': city
            })
            current_day += city_days
            remaining_days -= city_days
        
        if valid_path and remaining_days == 0:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Execute the function and print the result
result = find_valid_itinerary()
print(json.dumps(result))