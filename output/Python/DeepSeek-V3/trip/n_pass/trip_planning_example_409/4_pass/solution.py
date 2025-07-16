import json
from itertools import permutations

def find_itinerary():
    # Define constraints
    total_days = 12
    city_days = {
        'Hamburg': 2,
        'Zurich': 3,  # Zurich is spelled as Zurich in flight list
        'Helsinki': 2,
        'Bucharest': 2,
        'Split': 3
    }
    cities = list(city_days.keys())
    wedding_constraint = (1, 3)  # Wedding in Zurich between day 1 and day 3
    conference_days = {4, 10}  # Conference in Split on day 4 and day 10
    
    # Define direct flights as adjacency list
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Hamburg': ['Zurich', 'Helsinki', 'Bucharest', 'Split'],
        'Bucharest': ['Zurich', 'Hamburg'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    # Correct spelling inconsistencies
    flight_map = {
        'Zurich': 'Zurich',
        'Helsinki': 'Helsinki',
        'Helsinki': 'Helsinki',
        'Hamburg': 'Hamburg',
        'Bucharest': 'Bucharest',
        'Split': 'Split'
    }
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        # Try all possible day assignments that satisfy:
        # 1. Total days = 12
        # 2. City day requirements
        # 3. Conference days in Split
        # 4. Wedding in Zurich days 1-3
        
        # We'll represent the itinerary as a list of (city, start_day, end_day)
        itinerary = []
        current_day = 1
        
        # Track remaining days for each city
        remaining_days = city_days.copy()
        remaining_conf_days = conference_days.copy()
        wedding_satisfied = False
        
        valid = True
        
        for city in perm:
            if not valid:
                break
                
            days_needed = remaining_days[city]
            
            # Find earliest possible start day that:
            # 1. Leaves enough days remaining (current_day + days_needed - 1 <= 12)
            # 2. For Split, must include conference days 4 and 10
            # 3. For Zurich, must include at least one day between 1-3
            
            # Calculate possible start days
            max_start_day = total_days - days_needed + 1
            possible_starts = range(current_day, max_start_day + 1)
            
            # Filter based on city-specific constraints
            if city == 'Zurich':
                # Must overlap with days 1-3
                possible_starts = [s for s in possible_starts 
                                  if s <= 3 and s + days_needed - 1 >= 1]
                if not possible_starts:
                    valid = False
                    break
            
            if city == 'Split':
                # Must include both conference days
                possible_starts = [s for s in possible_starts 
                                 if s <= min(conference_days) and 
                                    s + days_needed - 1 >= max(conference_days)]
                if not possible_starts:
                    valid = False
                    break
            
            # Choose the earliest possible start day
            if possible_starts:
                start_day = possible_starts[0]
            else:
                valid = False
                break
            
            end_day = start_day + days_needed - 1
            
            # Check flight connections
            if itinerary:
                prev_city, prev_start, prev_end = itinerary[-1]
                if city not in direct_flights.get(prev_city, []):
                    valid = False
                    break
            
            # Add to itinerary
            itinerary.append((city, start_day, end_day))
            current_day = end_day + 1
            remaining_days[city] = 0
            
            # Check conference days for Split
            if city == 'Split':
                visit_days = set(range(start_day, end_day + 1))
                if not conference_days.issubset(visit_days):
                    valid = False
                    break
            
            # Check wedding for Zurich
            if city == 'Zurich':
                visit_days = set(range(start_day, end_day + 1))
                if not visit_days.intersection(range(wedding_constraint[0], wedding_constraint[1] + 1)):
                    valid = False
                    break
        
        # Check all constraints are satisfied
        if (valid and current_day - 1 == total_days 
            and all(v == 0 for v in remaining_days.values())
            and len(remaining_conf_days) == 0
            and wedding_satisfied):
            # Format the itinerary
            formatted_itinerary = []
            for city, start, end in itinerary:
                formatted_itinerary.append({
                    'day_range': f"Day {start}-{end}",
                    'place': city
                })
            return {"itinerary": formatted_itinerary}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))