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
        days_assigned = [False] * 13  # 1-based indexing for days 1-12
        remaining_days = cities.copy()
        itinerary = []
        
        # Prague must be first or last and cover days 1-2
        if order[0] == 'Prague':
            # Assign Prague to days 1-2
            if days_assigned[1] or days_assigned[2]:
                continue
            itinerary.append({'day_range': 'Day 1-2', 'place': 'Prague'})
            for day in range(1, 3):
                days_assigned[day] = True
            remaining_days['Prague'] -= 2
        elif order[-1] == 'Prague':
            # Assign Prague to days 11-12
            if days_assigned[11] or days_assigned[12]:
                continue
            itinerary.append({'day_range': 'Day 11-12', 'place': 'Prague'})
            for day in range(11, 13):
                days_assigned[day] = True
            remaining_days['Prague'] -= 2
        else:
            continue
        
        # Helsinki must be in the middle and cover days 2-5
        if 'Helsinki' not in order[1:-1]:
            continue
        
        helsinki_pos = order.index('Helsinki')
        
        # Assign Helsinki to days 2-5
        if any(days_assigned[d] for d in range(2, 6)):
            continue
        
        itinerary.append({'day_range': 'Day 2-5', 'place': 'Helsinki'})
        for day in range(2, 6):
            days_assigned[day] = True
        remaining_days['Helsinki'] -= 4
        
        # Assign remaining cities
        current_day = 1
        success = True
        
        for city in order:
            if city in ['Prague', 'Helsinki']:
                continue
            
            days_needed = remaining_days[city]
            
            # Find next available block of days
            while current_day <= 12 and days_assigned[current_day]:
                current_day += 1
            
            if current_day > 12:
                success = False
                break
            
            # Find consecutive available days
            end_day = current_day + days_needed - 1
            if end_day > 12:
                success = False
                break
                
            if any(days_assigned[d] for d in range(current_day, end_day + 1)):
                success = False
                break
            
            itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': city})
            for day in range(current_day, end_day + 1):
                days_assigned[day] = True
            current_day = end_day + 1
        
        # Check if all days are filled and all cities are fully assigned
        if success and all(days_assigned[1:13]) and all(v == 0 for v in remaining_days.values()):
            # Sort itinerary by day range
            sorted_itinerary = sorted(itinerary, key=lambda x: int(x['day_range'].split('-')[0].split(' ')[1]))
            valid_itineraries.append(sorted_itinerary)
    
    if valid_itineraries:
        # Return the first valid itinerary found
        return {"itinerary": valid_itineraries[0]}
    else:
        return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))