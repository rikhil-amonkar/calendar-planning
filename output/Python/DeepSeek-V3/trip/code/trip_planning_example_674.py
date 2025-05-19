import json
from itertools import permutations

def find_itinerary():
    # Input parameters
    cities = {
        'Helsinki': {'days': 2, 'constraint': (1, 2)},
        'Warsaw': {'days': 3, 'constraint': (9, 11)},
        'Madrid': {'days': 4, 'constraint': None},
        'Split': {'days': 4, 'constraint': None},
        'Reykjavik': {'days': 2, 'constraint': (8, 9)},
        'Budapest': {'days': 4, 'constraint': None}
    }
    
    direct_flights = {
        'Helsinki': ['Reykjavik', 'Split', 'Madrid', 'Budapest', 'Warsaw'],
        'Reykjavik': ['Helsinki', 'Warsaw', 'Madrid', 'Budapest'],
        'Budapest': ['Warsaw', 'Madrid', 'Reykjavik', 'Helsinki'],
        'Warsaw': ['Budapest', 'Reykjavik', 'Madrid', 'Split', 'Helsinki'],
        'Madrid': ['Split', 'Helsinki', 'Budapest', 'Warsaw', 'Reykjavik'],
        'Split': ['Madrid', 'Helsinki', 'Warsaw']
    }
    
    total_days = 14
    
    # Generate all possible permutations of the cities
    city_names = list(cities.keys())
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if Helsinki is first (due to day 1-2 constraint)
        if perm[0] != 'Helsinki':
            continue
        
        # Check if Reykjavik is visited before day 8-9
        reykjavik_pos = perm.index('Reykjavik')
        if reykjavik_pos == len(perm) - 1:
            # Reykjavik is last, which is too late
            continue
        
        # Check if Warsaw is visited around day 9-11
        warsaw_pos = perm.index('Warsaw')
        if warsaw_pos == 0:
            # Warsaw is first, which is too early
            continue
        
        prev_city = None
        for city in perm:
            if prev_city is not None:
                # Check if there's a direct flight
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                # Add flight day
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 1  # Flight takes a day
            
            # Add stay in the city
            days = cities[city]['days']
            constraint = cities[city]['constraint']
            end_day = current_day + days - 1
            
            if constraint is not None:
                if city == 'Helsinki':
                    if not (current_day <= constraint[0] and end_day >= constraint[1]):
                        valid = False
                        break
                elif city == 'Warsaw':
                    if not (current_day <= constraint[0] and end_day >= constraint[1]):
                        valid = False
                        break
                elif city == 'Reykjavik':
                    if not (current_day <= constraint[0] and end_day >= constraint[1]):
                        valid = False
                        break
            
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            current_day = end_day + 1
            prev_city = city
        
        # Check if total days is 14 and all constraints are met
        if valid and current_day - 1 == total_days:
            # Verify all cities are included
            visited_cities = {item['place'] for item in itinerary if 'place' in item}
            if len(visited_cities) == 6:
                return itinerary
    
    return None

itinerary = find_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps([{"error": "No valid itinerary found"}], indent=2))