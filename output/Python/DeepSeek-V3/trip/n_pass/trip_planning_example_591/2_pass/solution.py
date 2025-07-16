import json
from itertools import permutations

def find_valid_itinerary():
    # Cities and their required total stay durations
    cities = {
        'Stuttgart': 2,
        'Bucharest': 2,
        'Geneva': 4,
        'Valencia': 6,
        'Munich': 7  # Corrected spelling to match connections
    }
    
    # Direct flight connections
    connections = {
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Bucharest': ['Valencia', 'Munich'],
        'Stuttgart': ['Valencia']
    }
    
    # Constraints
    geneva_constraint = (1, 4)  # Must be in Geneva between day 1 and day 4
    munich_constraint = (4, 10)  # Must be in Munich between day 4 and day 10
    
    # Generate all possible permutations of the cities (allowing multiple visits)
    # We'll use backtracking to build the itinerary day by day
    def backtrack(current_itinerary, current_day, remaining_days, last_city):
        if current_day > 17:
            if all(v == 0 for v in remaining_days.values()):
                return current_itinerary
            return None
        
        # If we've used all required days, fill remaining with any valid city
        if all(v == 0 for v in remaining_days.values()):
            return None
        
        # Try all possible next cities
        for city in remaining_days:
            if remaining_days[city] == 0:
                continue
            if last_city and city not in connections[last_city]:
                continue
            
            # Determine maximum possible stay at this city
            max_stay = min(remaining_days[city], 17 - current_day + 1)
            
            # Try stays from 1 to max_stay days
            for stay in range(1, max_stay + 1):
                new_remaining = remaining_days.copy()
                new_remaining[city] -= stay
                
                # Check if this stay would satisfy constraints if applicable
                if city == 'Geneva':
                    if not (current_day <= geneva_constraint[1] and (current_day + stay - 1) >= geneva_constraint[0]):
                        continue
                if city == 'Munich':
                    if not (current_day <= munich_constraint[1] and (current_day + stay - 1) >= munich_constraint[0]):
                        continue
                
                new_itinerary = current_itinerary.copy()
                new_itinerary.append({
                    'day_range': f"Day {current_day}-{current_day + stay - 1}",
                    'place': city
                })
                
                result = backtrack(new_itinerary, current_day + stay, new_remaining, city)
                if result is not None:
                    return result
        
        return None
    
    # Start with full remaining days
    remaining_days = cities.copy()
    
    # Try starting with each city that can be first (Geneva or Valencia)
    for start_city in ['Geneva', 'Valencia']:
        max_stay = min(remaining_days[start_city], 17)
        for stay in range(1, max_stay + 1):
            # Check if starting with Geneva satisfies its constraint
            if start_city == 'Geneva':
                if not (1 <= stay <= 4):
                    continue
            
            new_remaining = remaining_days.copy()
            new_remaining[start_city] -= stay
            
            itinerary = [{
                'day_range': f"Day 1-{stay}",
                'place': start_city
            }]
            
            result = backtrack(itinerary, stay + 1, new_remaining, start_city)
            if result is not None:
                # Verify all constraints are met
                geneva_ok = False
                munich_ok = False
                total_days = 0
                
                for entry in result:
                    city = entry['place']
                    start_day = int(entry['day_range'].split('-')[0].split(' ')[1])
                    end_day = int(entry['day_range'].split('-')[1])
                    total_days += end_day - start_day + 1
                    
                    if city == 'Geneva':
                        if start_day <= geneva_constraint[1] and end_day >= geneva_constraint[0]:
                            geneva_ok = True
                    if city == 'Munich':
                        if start_day <= munich_constraint[1] and end_day >= munich_constraint[0]:
                            munich_ok = True
                
                if geneva_ok and munich_ok and total_days == 17:
                    return {'itinerary': result}
    
    return {'itinerary': []}

# Execute the function and print the result as JSON
result = find_valid_itinerary()
print(json.dumps(result, indent=2))