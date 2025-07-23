import json
from itertools import permutations

def find_valid_itinerary():
    # Corrected total days (sum of city stays is 21, not 17)
    total_days = 21
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
        'Geneva': ['Munich', 'Valencia'],  # Fixed typo in 'Munich'
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
        
        for city in perm:
            city_days = city_stays[city]
            
            # Check if we have enough days left
            if city_days > remaining_days:
                valid_path = False
                break
            
            # Handle Geneva constraint
            if city == 'Geneva':
                # Must start between day 1-4 and end by day 4
                latest_start = geneva_constraint[1] - city_days + 1
                if latest_start < geneva_constraint[0]:
                    valid_path = False
                    break
                # Adjust current_day if needed
                if current_day > latest_start:
                    valid_path = False
                    break
                if current_day < geneva_constraint[0]:
                    current_day = geneva_constraint[0]
                geneva_assigned = True
            
            # Handle Munich constraint
            if city == 'Munich':
                # Must start between day 4-10 and end by day 10
                latest_start = munich_constraint[1] - city_days + 1
                if latest_start < munich_constraint[0]:
                    valid_path = False
                    break
                # Adjust current_day if needed
                if current_day > latest_start:
                    valid_path = False
                    break
                if current_day < munich_constraint[0]:
                    current_day = munich_constraint[0]
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