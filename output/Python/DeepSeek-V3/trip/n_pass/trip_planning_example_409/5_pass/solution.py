import json
from itertools import permutations

def find_itinerary():
    # Define constraints
    total_days = 12
    city_days = {
        'Hamburg': 2,
        'Zurich': 3,
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
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        # We'll represent the itinerary as a list of (city, day)
        day_assignments = [None] * (total_days + 1)  # 1-based indexing
        remaining_days = city_days.copy()
        remaining_conf_days = conference_days.copy()
        wedding_satisfied = False
        
        # Try to assign days to this permutation
        valid = True
        current_day = 1
        
        for city in perm:
            if not valid:
                break
                
            days_needed = remaining_days[city]
            
            # Find earliest possible start day that:
            # 1. Leaves enough days remaining (current_day + days_needed - 1 <= 12)
            # 2. For Zurich, must include at least one day between 1-3
            # 3. For Split, must include conference days 4 and 10 (can be in separate visits)
            
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
            
            # Choose the earliest possible start day
            if possible_starts:
                start_day = possible_starts[0]
            else:
                valid = False
                break
            
            end_day = start_day + days_needed - 1
            
            # Check flight connections
            if start_day > 1:
                prev_day = start_day - 1
                prev_city = day_assignments[prev_day]
                if prev_city and city not in direct_flights.get(prev_city, []):
                    valid = False
                    break
            
            # Assign days
            for day in range(start_day, end_day + 1):
                day_assignments[day] = city
            
            # Update remaining days
            remaining_days[city] = 0
            
            # Check wedding for Zurich
            if city == 'Zurich':
                visit_days = set(range(start_day, end_day + 1))
                if visit_days.intersection(range(wedding_constraint[0], wedding_constraint[1] + 1)):
                    wedding_satisfied = True
            
            current_day = end_day + 1
        
        # After assigning all cities, check all constraints
        if valid:
            # Check all days are assigned
            if None in day_assignments[1:]:
                valid = False
            
            # Check conference days
            for day in conference_days:
                if day_assignments[day] != 'Split':
                    valid = False
            
            # Check wedding was satisfied
            if not wedding_satisfied:
                valid = False
            
            # Check all city days are satisfied
            city_counts = {}
            for day in range(1, total_days + 1):
                city = day_assignments[day]
                city_counts[city] = city_counts.get(city, 0) + 1
            for city, needed in city_days.items():
                if city_counts.get(city, 0) != needed:
                    valid = False
            
            if valid:
                # Format the itinerary by grouping consecutive days
                formatted_itinerary = []
                current_city = day_assignments[1]
                start_day = 1
                
                for day in range(2, total_days + 1):
                    if day_assignments[day] == current_city:
                        continue
                    else:
                        formatted_itinerary.append({
                            'day_range': f"Day {start_day}-{day-1}",
                            'place': current_city
                        })
                        current_city = day_assignments[day]
                        start_day = day
                
                # Add the last segment
                formatted_itinerary.append({
                    'day_range': f"Day {start_day}-{total_days}",
                    'place': current_city
                })
                
                return {"itinerary": formatted_itinerary}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))