import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    city_days = {
        'Split': 2,
        'Helsinki': 2,
        'Reykjavik': 3,
        'Vilnius': 3,
        'Geneva': 6
    }
    
    # Flight connections
    connections = {
        'Split': ['Helsinki', 'Geneva', 'Vilnius'],
        'Helsinki': ['Split', 'Geneva', 'Reykjavik', 'Vilnius'],
        'Geneva': ['Split', 'Helsinki'],
        'Reykjavik': ['Helsinki'],
        'Vilnius': ['Helsinki', 'Split']
    }
    
    # Special constraints
    wedding_constraint = {'city': 'Reykjavik', 'day_range': (10, 12)}
    relatives_constraint = {'city': 'Vilnius', 'day_range': (7, 9)}
    
    total_days = 12
    
    # Generate all possible city orders (permutations)
    cities = list(city_days.keys())
    possible_orders = permutations(cities)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if all transitions are possible
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in connections[order[i]]:
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Try to build the itinerary with constraints
        itinerary = []
        remaining_cities = set(order)
        used_days = set()
        
        # First place the constrained cities
        constrained_cities = [
            (wedding_constraint['city'], wedding_constraint['day_range']),
            (relatives_constraint['city'], relatives_constraint['day_range'])
        ]
        
        # Try placing constrained cities first
        temp_itinerary = []
        days_allocated = set()
        
        # Place Reykjavik (wedding)
        reykjavik_days = city_days['Reykjavik']
        wedding_start, wedding_end = wedding_constraint['day_range']
        latest_start = wedding_end - reykjavik_days + 1
        reykjavik_start = max(wedding_start, latest_start)
        reykjavik_end = reykjavik_start + reykjavik_days - 1
        
        if reykjavik_start > latest_start:
            continue  # Can't satisfy wedding constraint
        
        # Check if Reykjavik is in this order
        if 'Reykjavik' not in order:
            continue
            
        # Place Vilnius (relatives)
        vilnius_days = city_days['Vilnius']
        relatives_start, relatives_end = relatives_constraint['day_range']
        latest_vilnius_start = relatives_end - vilnius_days + 1
        vilnius_start = max(relatives_start, latest_vilnius_start)
        vilnius_end = vilnius_start + vilnius_days - 1
        
        if vilnius_start > latest_vilnius_start:
            continue  # Can't satisfy relatives constraint
        
        if 'Vilnius' not in order:
            continue
            
        # Now try to place these constrained cities in the order
        # while maintaining flight connections
        
        # Find positions of constrained cities in the order
        try:
            reykjavik_pos = order.index('Reykjavik')
            vilnius_pos = order.index('Vilnius')
        except ValueError:
            continue
            
        # Check if the order between constrained cities makes sense
        if reykjavik_pos < vilnius_pos:
            # Need to place Vilnius after Reykjavik
            if vilnius_end > reykjavik_start:
                continue  # Overlapping constraints
        else:
            # Need to place Reykjavik after Vilnius
            if reykjavik_start < vilnius_end:
                continue  # Overlapping constraints
                
        # Now try to place all cities
        current_day = 1
        temp_itinerary = []
        remaining_cities = set(order)
        valid = True
        
        for city in order:
            if city not in remaining_cities:
                continue
                
            required_days = city_days[city]
            
            if city == 'Reykjavik':
                start_day = reykjavik_start
                end_day = reykjavik_end
            elif city == 'Vilnius':
                start_day = vilnius_start
                end_day = vilnius_end
            else:
                # Place non-constrained city in earliest available spot
                start_day = current_day
                end_day = start_day + required_days - 1
                
                # Check for overlaps with constrained cities
                if (start_day <= reykjavik_end and end_day >= reykjavik_start) or \
                   (start_day <= vilnius_end and end_day >= vilnius_start):
                    # Find next available spot
                    start_day = max(current_day, reykjavik_end + 1, vilnius_end + 1)
                    end_day = start_day + required_days - 1
                    
            if end_day > total_days:
                valid = False
                break
                
            temp_itinerary.append({
                'day_range': f"{start_day}-{end_day}",
                'place': city
            })
            remaining_cities.remove(city)
            current_day = end_day + 1
            
        if valid and not remaining_cities:
            # Verify all constraints are met
            wedding_ok = False
            relatives_ok = False
            for entry in temp_itinerary:
                if entry['place'] == 'Reykjavik':
                    start, end = map(int, entry['day_range'].split('-'))
                    if start <= wedding_start and end >= wedding_end:
                        wedding_ok = True
                if entry['place'] == 'Vilnius':
                    start, end = map(int, entry['day_range'].split('-'))
                    if start <= relatives_start and end >= relatives_end:
                        relatives_ok = True
            
            if wedding_ok and relatives_ok:
                # Format the itinerary
                formatted_itinerary = []
                for entry in temp_itinerary:
                    formatted_itinerary.append({
                        'day_range': f"Day {entry['day_range']}",
                        'place': entry['place']
                    })
                valid_itineraries.append(formatted_itinerary)
    
    if not valid_itineraries:
        return {"error": "No valid itinerary found with given constraints"}
    
    # Return the first valid itinerary found
    return {"itinerary": valid_itineraries[0]}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))