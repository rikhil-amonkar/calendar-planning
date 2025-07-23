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
        
        # Try all possible day assignments for this order
        current_day = 1
        itinerary = []
        remaining_cities = list(order)
        
        # We'll try to place constrained cities first
        constrained_cities = [wedding_constraint['city'], relatives_constraint['city']]
        
        # Create a list of cities to place, with constrained ones first
        cities_to_place = [c for c in order if c in constrained_cities]
        cities_to_place += [c for c in order if c not in constrained_cities]
        
        # Try to build the itinerary
        temp_itinerary = []
        day = 1
        valid = True
        
        for city in cities_to_place:
            required_days = city_days[city]
            
            # Check if this city has constraints
            if city == wedding_constraint['city']:
                start, end = wedding_constraint['day_range']
                # Must be placed to cover days 10-12
                latest_start = end - required_days + 1
                earliest_start = start
                
                # Find a position that satisfies this
                if day > latest_start:
                    valid = False
                    break
                
                if day < earliest_start:
                    # We need to fill the gap before placing Reykjavik
                    gap_days = earliest_start - day
                    # Try to find cities that can fill this gap
                    gap_filled = False
                    for other_city in [c for c in remaining_cities if c != city]:
                        if city_days[other_city] == gap_days:
                            temp_itinerary.append({
                                'day_range': f"{day}-{day + gap_days - 1}",
                                'place': other_city
                            })
                            day += gap_days
                            remaining_cities.remove(other_city)
                            gap_filled = True
                            break
                    
                    if not gap_filled:
                        valid = False
                        break
                
                # Now place Reykjavik
                if day > latest_start:
                    valid = False
                    break
                
                temp_itinerary.append({
                    'day_range': f"{day}-{day + required_days - 1}",
                    'place': city
                })
                day += required_days
                remaining_cities.remove(city)
                
            elif city == relatives_constraint['city']:
                start, end = relatives_constraint['day_range']
                # Must be placed to cover days 7-9
                latest_start = end - required_days + 1
                earliest_start = start
                
                if day > latest_start:
                    valid = False
                    break
                
                if day < earliest_start:
                    # Fill gap before Vilnius
                    gap_days = earliest_start - day
                    for other_city in [c for c in remaining_cities if c != city]:
                        if city_days[other_city] == gap_days:
                            temp_itinerary.append({
                                'day_range': f"{day}-{day + gap_days - 1}",
                                'place': other_city
                            })
                            day += gap_days
                            remaining_cities.remove(other_city)
                            break
                    else:
                        valid = False
                        break
                
                # Place Vilnius
                if day > latest_start:
                    valid = False
                    break
                
                temp_itinerary.append({
                    'day_range': f"{day}-{day + required_days - 1}",
                    'place': city
                })
                day += required_days
                remaining_cities.remove(city)
                
            else:
                # Place non-constrained city if it fits
                if day + required_days - 1 > total_days:
                    valid = False
                    break
                
                temp_itinerary.append({
                    'day_range': f"{day}-{day + required_days - 1}",
                    'place': city
                })
                day += required_days
                remaining_cities.remove(city)
        
        if valid and day <= total_days + 1 and len(temp_itinerary) == len(order):
            # Verify all constraints are met
            wedding_ok = False
            relatives_ok = False
            for entry in temp_itinerary:
                if entry['place'] == wedding_constraint['city']:
                    start, end = map(int, entry['day_range'].split('-'))
                    if start <= wedding_constraint['day_range'][0] and end >= wedding_constraint['day_range'][1]:
                        wedding_ok = True
                if entry['place'] == relatives_constraint['city']:
                    start, end = map(int, entry['day_range'].split('-'))
                    if start <= relatives_constraint['day_range'][0] and end >= relatives_constraint['day_range'][1]:
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