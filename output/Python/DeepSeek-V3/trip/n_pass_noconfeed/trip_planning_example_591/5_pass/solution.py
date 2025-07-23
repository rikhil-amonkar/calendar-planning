import json
from itertools import permutations

def find_valid_itinerary():
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
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest', 'Stuttgart'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Bucharest': ['Valencia', 'Munich', 'Stuttgart'],
        'Stuttgart': ['Valencia', 'Bucharest', 'Munich']
    }
    
    # Generate all possible permutations of the cities
    cities = list(city_stays.keys())
    
    for perm in permutations(cities):
        # Check if the permutation is a valid path considering flight connections
        valid_path = True
        for i in range(len(perm) - 1):
            current_city = perm[i]
            next_city = perm[i+1]
            
            if next_city not in connections.get(current_city, []):
                valid_path = False
                break
        
        if not valid_path:
            continue
        
        # Try to assign days to the cities in this order
        itinerary = []
        current_day = 1
        remaining_days = total_days
        geneva_visited = False
        munich_visited = False
        
        for city in perm:
            stay_days = city_stays[city]
            
            # Check if we have enough days left
            if stay_days > remaining_days:
                valid_path = False
                break
            
            # Handle Geneva constraint
            if city == 'Geneva':
                # Must be completely within days 1-4
                earliest_start = geneva_constraint[0]
                latest_start = geneva_constraint[1] - stay_days + 1
                if current_day > latest_start:
                    valid_path = False
                    break
                if current_day < earliest_start:
                    current_day = earliest_start
                geneva_visited = True
            
            # Handle Munich constraint
            if city == 'Munich':
                # Must be completely within days 4-10
                earliest_start = munich_constraint[0]
                latest_start = munich_constraint[1] - stay_days + 1
                if current_day > latest_start:
                    valid_path = False
                    break
                if current_day < earliest_start:
                    current_day = earliest_start
                munich_visited = True
            
            # Add to itinerary
            itinerary.append({
                'day_range': f"Day {current_day}-{current_day + stay_days - 1}",
                'place': city
            })
            
            current_day += stay_days
            remaining_days -= stay_days
        
        # Check if all constraints are met
        if (valid_path and remaining_days == 0 and 
            geneva_visited and munich_visited):
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Execute the function and print the result
result = find_valid_itinerary()
print(json.dumps(result, indent=2))