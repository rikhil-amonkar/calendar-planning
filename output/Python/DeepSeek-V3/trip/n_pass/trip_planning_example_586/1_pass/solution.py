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
    helsinki_show_days = (2, 5)  # Day 2 to Day 5
    prague_workshop_days = (1, 2)  # Between Day 1 and Day 2
    
    # Generate all possible city orders
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if the order respects flight connections
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in connections.get(order[i], []):
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Assign days to cities respecting constraints
        itinerary = []
        current_day = 1
        remaining_days = cities.copy()
        
        # Assign Prague first due to workshop constraint
        if order[0] != 'Prague' and order[-1] != 'Prague':
            continue  # Prague must be first or last to fit workshop
        
        # Try to assign Prague first
        if order[0] == 'Prague':
            # Prague must include day 1-2
            itinerary.append({'day_range': f'Day 1-2', 'place': 'Prague'})
            remaining_days['Prague'] -= 2
            current_day = 3
        else:
            # Prague must be last, but can't fit workshop
            continue
        
        # Assign Helsinki show days (2-5)
        if 'Helsinki' in order:
            helsinki_pos = order.index('Helsinki')
            if helsinki_pos == 1:  # Second city
                start_day = max(current_day, 2)
                end_day = start_day + 3  # 4 days total (start_day to end_day inclusive)
                if end_day > 5:
                    continue  # Doesn't fit show constraint
                itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Helsinki'})
                remaining_days['Helsinki'] -= (end_day - start_day + 1)
                current_day = end_day + 1
            else:
                # Helsinki must be second to fit show days
                continue
        
        # Assign remaining cities
        for city in order[1:]:
            if city == 'Prague' or city == 'Helsinki':
                continue  # Already assigned
            
            days_needed = remaining_days[city]
            if current_day + days_needed - 1 > 12:
                valid_order = False
                break
            
            itinerary.append({'day_range': f'Day {current_day}-{current_day + days_needed - 1}', 'place': city})
            current_day += days_needed
        
        # Check if all days are assigned and constraints met
        if valid_order and current_day - 1 == 12 and all(v == 0 for v in remaining_days.values()):
            valid_itineraries.append(itinerary)
    
    if valid_itineraries:
        # Return the first valid itinerary found
        return {"itinerary": valid_itineraries[0]}
    else:
        return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result))