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
        
        # Initialize day tracking
        current_day = 1
        itinerary = []
        remaining_cities = list(order)
        
        # First handle cities with constraints
        constrained_cities = [wedding_constraint['city'], relatives_constraint['city']]
        
        # Try to assign constrained cities first
        for city in constrained_cities:
            if city in remaining_cities:
                required_days = city_days[city]
                
                # Get the constraint for this city
                if city == wedding_constraint['city']:
                    start, end = wedding_constraint['day_range']
                else:
                    start, end = relatives_constraint['day_range']
                
                # Calculate the latest day we can start to meet the constraint
                latest_start = end - required_days + 1
                if latest_start < 1:
                    valid_order = False
                    break
                
                # Find a position in the itinerary where we can place this city
                placed = False
                for pos in range(len(itinerary) + 1):
                    # Calculate the day this city would start if inserted here
                    if pos == 0:
                        new_start = current_day
                    else:
                        new_start = int(itinerary[pos-1]['day_range'].split('-')[1]) + 1
                    
                    # Check if this position works
                    if new_start <= latest_start and (new_start + required_days - 1) >= start:
                        # Insert the city here
                        day_range = f"{new_start}-{new_start + required_days - 1}"
                        itinerary.insert(pos, {
                            'day_range': day_range,
                            'place': city
                        })
                        remaining_cities.remove(city)
                        placed = True
                        break
                
                if not placed:
                    valid_order = False
                    break
        
        if not valid_order:
            continue
        
        # Now assign remaining cities to fill the gaps
        full_itinerary = []
        prev_end = 0
        
        for entry in itinerary:
            start_day = int(entry['day_range'].split('-')[0])
            # Fill any gap before this entry
            if start_day > prev_end + 1:
                gap_days = start_day - prev_end - 1
                # Find a city that fits in this gap
                for city in remaining_cities:
                    if city_days[city] == gap_days:
                        full_itinerary.append({
                            'day_range': f"{prev_end + 1}-{prev_end + gap_days}",
                            'place': city
                        })
                        remaining_cities.remove(city)
                        break
            
            full_itinerary.append(entry)
            prev_end = int(entry['day_range'].split('-')[1])
        
        # Fill any remaining days at the end
        if prev_end < total_days:
            gap_days = total_days - prev_end
            for city in remaining_cities:
                if city_days[city] == gap_days:
                    full_itinerary.append({
                        'day_range': f"{prev_end + 1}-{total_days}",
                        'place': city
                    })
                    remaining_cities.remove(city)
                    break
        
        # Check if all cities were placed and constraints are met
        if len(remaining_cities) == 0 and len(full_itinerary) == len(cities):
            # Verify constraints
            wedding_ok = False
            relatives_ok = False
            for entry in full_itinerary:
                if entry['place'] == wedding_constraint['city']:
                    start, end = wedding_constraint['day_range']
                    day_start = int(entry['day_range'].split('-')[0])
                    day_end = int(entry['day_range'].split('-')[1])
                    if day_start <= start and day_end >= end:
                        wedding_ok = True
                if entry['place'] == relatives_constraint['city']:
                    start, end = relatives_constraint['day_range']
                    day_start = int(entry['day_range'].split('-')[0])
                    day_end = int(entry['day_range'].split('-')[1])
                    if day_start <= start and day_end >= end:
                        relatives_ok = True
            
            if wedding_ok and relatives_ok:
                # Format the day ranges nicely
                formatted_itinerary = []
                for entry in full_itinerary:
                    start, end = entry['day_range'].split('-')
                    formatted_itinerary.append({
                        'day_range': f"Day {start}-{end}",
                        'place': entry['place']
                    })
                valid_itineraries.append(formatted_itinerary)
    
    if not valid_itineraries:
        return {"error": "No valid itinerary found with given constraints"}
    
    # Sort itineraries by some criteria (e.g., earliest wedding)
    valid_itineraries.sort(key=lambda x: [
        int(entry['day_range'].split(' ')[1].split('-')[0]) 
        for entry in x 
        if entry['place'] == wedding_constraint['city']
    ][0])
    
    # Select the first valid itinerary
    selected_itinerary = valid_itineraries[0]
    
    return {"itinerary": selected_itinerary}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))