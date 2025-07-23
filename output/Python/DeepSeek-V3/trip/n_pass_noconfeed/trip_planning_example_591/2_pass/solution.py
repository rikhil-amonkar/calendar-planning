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
    geneva_constraint = (1, 4)  # Must be visited between day 1-4
    munich_constraint = (4, 10)  # Must be visited between day 4-10
    
    # Define the flight connections (direct flights between cities)
    connections = {
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Bucharest': ['Valencia', 'Munich'],
        'Stuttgart': ['Valencia']
    }
    
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
        current_day = 1
        remaining_days = total_days
        geneva_assigned = False
        munich_assigned = False
        
        # We'll process the permutation and assign days
        for city in perm:
            city_days = city_stays[city]
            
            # Check if we have enough days left
            if city_days > remaining_days:
                valid_path = False
                break
            
            # Handle Geneva constraint
            if city == 'Geneva':
                # Must be assigned between day 1-4
                if current_day > geneva_constraint[1]:
                    valid_path = False
                    break
                # Check if we can fit Geneva within its constraint
                end_day = current_day + city_days - 1
                if end_day > geneva_constraint[1]:
                    valid_path = False
                    break
                geneva_assigned = True
            
            # Handle Munich constraint
            if city == 'Munich':
                # Must be assigned between day 4-10
                if current_day > munich_constraint[1]:
                    valid_path = False
                    break
                # Check if we can fit Munich within its constraint
                end_day = current_day + city_days - 1
                if end_day < munich_constraint[0] or end_day > munich_constraint[1]:
                    valid_path = False
                    break
                munich_assigned = True
            
            # Add to itinerary
            itinerary.append({
                'day_range': f"Day {current_day}-{current_day + city_days - 1}",
                'place': city
            })
            
            current_day += city_days
            remaining_days -= city_days
        
        # Check if all constraints are met
        if (valid_path and remaining_days == 0 and 
            geneva_assigned and munich_assigned):
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Execute the function and print the result
result = find_valid_itinerary()
print(json.dumps(result, indent=2))