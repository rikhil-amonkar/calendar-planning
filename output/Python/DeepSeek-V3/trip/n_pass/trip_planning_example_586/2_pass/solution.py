import json
from itertools import permutations

def find_itinerary():
    # Define the cities and their required days
    cities = {
        'Frankfurt': 3,
        'Naples': 4,
        'Helsinki': 4,
        'Lyon': 3,
        'Prague': 2
    }
    
    # Define the direct flight connections
    connections = {
        'Prague': ['Lyon', 'Frankfurt', 'Helsinki'],
        'Lyon': ['Prague', 'Frankfurt'],
        'Frankfurt': ['Prague', 'Lyon', 'Helsinki', 'Naples'],
        'Helsinki': ['Prague', 'Frankfurt', 'Naples'],
        'Naples': ['Helsinki', 'Frankfurt']
    }
    
    # Fixed constraints
    helsinki_show_days = (2, 5)  # Must include days 2-5
    prague_workshop_days = (1, 2)  # Must include days 1-2
    
    # Generate all possible city orders
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check flight connections
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in connections.get(order[i], []):
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Try to assign days
        itinerary = []
        days_assigned = [False] * 13  # 1-based indexing for days 1-12
        remaining_days = cities.copy()
        
        # First assign Prague (must include days 1-2)
        if 'Prague' not in order:
            continue
        
        prague_pos = order.index('Prague')
        if prague_pos != 0 and prague_pos != len(order)-1:
            continue  # Prague must be first or last
        
        # Assign Prague days 1-2
        itinerary.append({'day_range': 'Day 1-2', 'place': 'Prague'})
        for day in range(1, 3):
            days_assigned[day] = True
        remaining_days['Prague'] -= 2
        
        # Assign Helsinki (must include days 2-5)
        if 'Helsinki' not in order:
            continue
        
        helsinki_pos = order.index('Helsinki')
        if helsinki_pos == 0 or helsinki_pos == len(order)-1:
            continue  # Helsinki can't be first or last (Prague is)
        
        # Find consecutive 4 days that include 2-5
        possible_helsinki_ranges = []
        for start in range(2, 4):  # Can start on day 2 or 3 to cover 2-5
            end = start + 3
            if end > 12:
                continue
            if all(not days_assigned[d] for d in range(start, end+1)):
                possible_helsinki_ranges.append((start, end))
        
        if not possible_helsinki_ranges:
            continue
        
        # Try each possible Helsinki range
        for start, end in possible_helsinki_ranges:
            temp_itinerary = itinerary.copy()
            temp_days_assigned = days_assigned.copy()
            temp_remaining = remaining_days.copy()
            
            temp_itinerary.append({'day_range': f'Day {start}-{end}', 'place': 'Helsinki'})
            for day in range(start, end+1):
                temp_days_assigned[day] = True
            temp_remaining['Helsinki'] -= 4
            
            # Assign remaining cities
            current_day = 1
            success = True
            temp_itinerary_full = temp_itinerary.copy()
            
            for city in order:
                if city in ['Prague', 'Helsinki']:
                    continue
                
                days_needed = temp_remaining[city]
                # Find next available block of days
                while current_day <= 12 and temp_days_assigned[current_day]:
                    current_day += 1
                
                if current_day + days_needed - 1 > 12:
                    success = False
                    break
                
                temp_itinerary_full.append({'day_range': f'Day {current_day}-{current_day + days_needed - 1}', 'place': city})
                for day in range(current_day, current_day + days_needed):
                    if temp_days_assigned[day]:
                        success = False
                        break
                    temp_days_assigned[day] = True
                if not success:
                    break
                current_day += days_needed
            
            if success and all(temp_days_assigned[1:13]) and all(v == 0 for v in temp_remaining.values()):
                valid_itineraries.append(temp_itinerary_full)
    
    if valid_itineraries:
        # Return the first valid itinerary found
        return {"itinerary": valid_itineraries[0]}
    else:
        return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))