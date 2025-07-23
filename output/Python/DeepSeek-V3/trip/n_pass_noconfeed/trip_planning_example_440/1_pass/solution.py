import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    city_days = {
        'Split': 2,
        'Helsinki': 2,  # Note: Original input says 'Helsinki' but later uses 'Helsinki' and 'Helsinki' interchangeably. Assuming typo.
        'Reykjavik': 3,
        'Vilnius': 3,
        'Geneva': 6
    }
    
    # Correcting the typo in city names to be consistent
    city_days['Helsinki'] = city_days.pop('Helsinki')
    
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
        
        # Try to assign days to this order
        itinerary = []
        remaining_days = total_days
        current_day = 1
        
        for city in order:
            required_days = city_days[city]
            
            # Check if the city has special constraints
            if city == wedding_constraint['city']:
                start, end = wedding_constraint['day_range']
                if current_day > end or (current_day + required_days - 1) < start:
                    valid_order = False
                    break
                # Adjust to fit the constraint
                if current_day < start:
                    # Need to be in this city by start day
                    days_before = start - current_day
                    # Assign days to previous cities to fit
                    # This is complex; for simplicity, we'll assume the order allows it
                    pass
            elif city == relatives_constraint['city']:
                start, end = relatives_constraint['day_range']
                if current_day > end or (current_day + required_days - 1) < start:
                    valid_order = False
                    break
            
            # Assign the days
            day_range_start = current_day
            day_range_end = current_day + required_days - 1
            itinerary.append({
                'day_range': f"Day {day_range_start}-{day_range_end}",
                'place': city
            })
            current_day += required_days
        
        if valid_order and current_day - 1 == total_days:
            # Check if special constraints are satisfied
            satisfied = True
            for entry in itinerary:
                if entry['place'] == wedding_constraint['city']:
                    start, end = wedding_constraint['day_range']
                    day_start = int(entry['day_range'].split(' ')[1].split('-')[0])
                    day_end = int(entry['day_range'].split(' ')[1].split('-')[1])
                    if not (day_start <= start and day_end >= end):
                        satisfied = False
                        break
                if entry['place'] == relatives_constraint['city']:
                    start, end = relatives_constraint['day_range']
                    day_start = int(entry['day_range'].split(' ')[1].split('-')[0])
                    day_end = int(entry['day_range'].split(' ')[1].split('-')[1])
                    if not (day_start <= start and day_end >= end):
                        satisfied = False
                        break
            if satisfied:
                valid_itineraries.append(itinerary)
    
    if not valid_itineraries:
        return {"error": "No valid itinerary found with given constraints"}
    
    # Select the first valid itinerary (could be optimized further)
    selected_itinerary = valid_itineraries[0]
    
    return {"itinerary": selected_itinerary}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result))