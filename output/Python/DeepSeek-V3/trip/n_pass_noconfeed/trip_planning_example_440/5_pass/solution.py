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
        
        # Try to build the itinerary
        itinerary = []
        remaining_days = set(range(1, total_days + 1))
        placed_cities = set()
        
        # First place the constrained cities
        constrained_cities = [
            ('Reykjavik', wedding_constraint['day_range'], city_days['Reykjavik']),
            ('Vilnius', relatives_constraint['day_range'], city_days['Vilnius'])
        ]
        
        # Try placing constrained cities first
        temp_itinerary = []
        days_allocated = set()
        
        # Place Reykjavik (wedding)
        reykjavik_days = city_days['Reykjavik']
        wedding_start, wedding_end = wedding_constraint['day_range']
        reykjavik_start = wedding_end - reykjavik_days + 1
        reykjavik_end = wedding_end
        
        if reykjavik_start < wedding_start:
            reykjavik_start = wedding_start
            reykjavik_end = reykjavik_start + reykjavik_days - 1
        
        if reykjavik_end > total_days:
            continue
            
        reykjavik_days_set = set(range(reykjavik_start, reykjavik_end + 1))
        
        # Place Vilnius (relatives)
        vilnius_days = city_days['Vilnius']
        relatives_start, relatives_end = relatives_constraint['day_range']
        vilnius_start = relatives_end - vilnius_days + 1
        vilnius_end = relatives_end
        
        if vilnius_start < relatives_start:
            vilnius_start = relatives_start
            vilnius_end = vilnius_start + vilnius_days - 1
        
        if vilnius_end > total_days:
            continue
            
        vilnius_days_set = set(range(vilnius_start, vilnius_end + 1))
        
        # Check if constrained cities overlap
        if reykjavik_days_set & vilnius_days_set:
            continue
            
        # Check if both constrained cities are in this order
        if 'Reykjavik' not in order or 'Vilnius' not in order:
            continue
            
        # Now try to place all cities in order
        current_day = 1
        temp_itinerary = []
        placed_cities = set()
        valid = True
        
        for city in order:
            if city in placed_cities:
                continue
                
            required_days = city_days[city]
            
            if city == 'Reykjavik':
                start_day = reykjavik_start
                end_day = reykjavik_end
            elif city == 'Vilnius':
                start_day = vilnius_start
                end_day = vilnius_end
            else:
                # Find earliest available consecutive days
                start_day = current_day
                end_day = start_day + required_days - 1
                
                # Adjust for constrained cities
                while True:
                    # Check if overlaps with constrained cities
                    days_requested = set(range(start_day, end_day + 1))
                    if days_requested & reykjavik_days_set or days_requested & vilnius_days_set:
                        start_day = max(start_day + 1, 
                                      reykjavik_end + 1 if start_day <= reykjavik_end else current_day,
                                      vilnius_end + 1 if start_day <= vilnius_end else current_day)
                        end_day = start_day + required_days - 1
                    else:
                        break
                        
                    if end_day > total_days:
                        valid = False
                        break
                
                if not valid:
                    break
                    
            if end_day > total_days:
                valid = False
                break
                
            temp_itinerary.append({
                'day_range': f"{start_day}-{end_day}",
                'place': city
            })
            placed_cities.add(city)
            current_day = end_day + 1
            
        if valid and len(placed_cities) == len(cities):
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
                for entry in sorted(temp_itinerary, key=lambda x: int(x['day_range'].split('-')[0])):
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