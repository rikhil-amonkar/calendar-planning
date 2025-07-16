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
            current_city = order[i]
            next_city = order[i+1]
            if next_city not in connections.get(current_city, []):
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Initialize day assignments
        days_assigned = [False] * 13  # 1-based indexing for days 1-12
        itinerary = []
        remaining_days = cities.copy()
        
        # Try to place Prague first or last
        if order[0] == 'Prague':
            # Assign Prague to days 1-2
            if not days_assigned[1] and not days_assigned[2]:
                itinerary.append({'day_range': 'Day 1-2', 'place': 'Prague'})
                for day in range(1, 3):
                    days_assigned[day] = True
                remaining_days['Prague'] = 0
            else:
                continue
        elif order[-1] == 'Prague':
            # Assign Prague to days 11-12
            if not days_assigned[11] and not days_assigned[12]:
                itinerary.append({'day_range': 'Day 11-12', 'place': 'Prague'})
                for day in range(11, 13):
                    days_assigned[day] = True
                remaining_days['Prague'] = 0
            else:
                continue
        else:
            continue
        
        # Try to place Helsinki in the middle (not first or last)
        if 'Helsinki' not in order[1:-1]:
            continue
        
        # Find available 4-day block for Helsinki
        helsinki_assigned = False
        for start_day in range(2, 9):  # Can't start later than day 9 (9-12)
            end_day = start_day + 3
            if end_day > 12:
                continue
            if not any(days_assigned[d] for d in range(start_day, end_day + 1)):
                itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Helsinki'})
                for day in range(start_day, end_day + 1):
                    days_assigned[day] = True
                remaining_days['Helsinki'] = 0
                helsinki_assigned = True
                break
        
        if not helsinki_assigned:
            continue
        
        # Assign remaining cities
        for city in order:
            if city in ['Prague', 'Helsinki']:
                continue
            
            days_needed = remaining_days[city]
            if days_needed <= 0:
                continue
            
            # Find next available block of days
            assigned = False
            for start_day in range(1, 13 - days_needed + 1):
                end_day = start_day + days_needed - 1
                if not any(days_assigned[d] for d in range(start_day, end_day + 1)):
                    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                    for day in range(start_day, end_day + 1):
                        days_assigned[day] = True
                    remaining_days[city] = 0
                    assigned = True
                    break
            
            if not assigned:
                break
        
        # Check if all days are filled and all cities are fully assigned
        if all(days_assigned[1:13]) and all(v == 0 for v in remaining_days.values()):
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