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
        days_assigned = [False] * 13  # 1-based indexing for days 1-12
        remaining_days = cities.copy()
        itinerary = []
        
        # Assign Prague first (must be first or last, and must cover days 1-2)
        if order[0] != 'Prague' and order[-1] != 'Prague':
            continue
        
        if order[0] == 'Prague':
            # Assign Prague to days 1-2
            itinerary.append({'day_range': 'Day 1-2', 'place': 'Prague'})
            for day in range(1, 3):
                days_assigned[day] = True
            remaining_days['Prague'] -= 2
        else:
            # Prague is last - we'll handle this case separately
            continue
        
        # Find Helsinki in the order (must be middle city)
        if 'Helsinki' not in order[1:-1]:
            continue
        
        helsinki_pos = order.index('Helsinki')
        helsinki_start = None
        
        # Helsinki must cover days 2-5 (4 consecutive days)
        # Possible Helsinki assignments:
        # Option 1: Days 2-5
        if all(not days_assigned[d] for d in range(2, 6)):
            helsinki_start = 2
        # Option 2: Days 1-4 (but conflicts with Prague)
        # Option 3: Days 3-6 (but would miss day 2)
        # Only Option 1 is valid
        
        if helsinki_start is None:
            continue
        
        # Assign Helsinki to days 2-5
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
            
            if current_day + days_needed - 1 > 12:
                success = False
                break
            
            # Check if this assignment would overlap with Helsinki
            if any(days_assigned[d] for d in range(current_day, current_day + days_needed)):
                success = False
                break
            
            itinerary.append({'day_range': f'Day {current_day}-{current_day + days_needed - 1}', 'place': city})
            for day in range(current_day, current_day + days_needed):
                days_assigned[day] = True
            current_day += days_needed
        
        if success and all(days_assigned[1:13]) and all(v == 0 for v in remaining_days.values()):
            valid_itineraries.append(itinerary)
    
    if valid_itineraries:
        # Return the first valid itinerary found
        return {"itinerary": valid_itineraries[0]}
    else:
        return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))