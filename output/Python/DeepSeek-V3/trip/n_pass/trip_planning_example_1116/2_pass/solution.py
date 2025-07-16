import json
from itertools import permutations

def find_itinerary():
    # Define constraints
    total_days = 20
    city_days = {
        'Oslo': 2,
        'Reykjavik': 5,
        'Stockholm': 4,
        'Munich': 4,
        'Frankfurt': 4,
        'Barcelona': 3,
        'Bucharest': 2,
        'Split': 3
    }
    
    # Define flight connections
    flights = {
        'Reykjavik': ['Munich', 'Frankfurt', 'Oslo', 'Barcelona', 'Stockholm'],
        'Munich': ['Reykjavik', 'Frankfurt', 'Bucharest', 'Oslo', 'Stockholm', 'Split', 'Barcelona'],
        'Frankfurt': ['Munich', 'Oslo', 'Bucharest', 'Barcelona', 'Reykjavik', 'Stockholm', 'Split'],
        'Oslo': ['Split', 'Reykjavik', 'Frankfurt', 'Bucharest', 'Barcelona', 'Stockholm', 'Munich'],
        'Bucharest': ['Munich', 'Barcelona', 'Oslo', 'Frankfurt'],
        'Barcelona': ['Bucharest', 'Frankfurt', 'Reykjavik', 'Stockholm', 'Split', 'Oslo', 'Munich'],
        'Stockholm': ['Barcelona', 'Reykjavik', 'Split', 'Munich', 'Oslo', 'Frankfurt'],
        'Split': ['Oslo', 'Barcelona', 'Stockholm', 'Frankfurt', 'Munich']
    }
    
    # Define fixed events (city: required day range)
    fixed_events = {
        'Oslo': (16, 17),
        'Reykjavik': (9, 13),
        'Munich': (13, 16),
        'Frankfurt': (17, 20)
    }
    
    # Generate all possible city orders (permutations)
    cities = [city for city in city_days if city not in fixed_events]
    fixed_cities = list(fixed_events.keys())
    
    # We'll try all permutations of non-fixed cities and insert fixed cities appropriately
    for perm in permutations(cities):
        # Try all possible ways to insert fixed cities into the permutation
        for fixed_perm in permutations(fixed_cities):
            full_order = []
            fixed_ptr = 0
            perm_ptr = 0
            
            # Interleave fixed and non-fixed cities (all possible orders)
            while fixed_ptr < len(fixed_perm) or perm_ptr < len(perm):
                if fixed_ptr < len(fixed_perm) and (perm_ptr >= len(perm) or (fixed_ptr <= perm_ptr)):
                    full_order.append(fixed_perm[fixed_ptr])
                    fixed_ptr += 1
                else:
                    full_order.append(perm[perm_ptr])
                    perm_ptr += 1
            
            # Now check if this order satisfies all constraints
            itinerary = []
            current_day = 1
            prev_city = None
            valid = True
            
            for city in full_order:
                # Check flight connection
                if prev_city is not None and city not in flights[prev_city]:
                    valid = False
                    break
                
                days = city_days[city]
                day_end = current_day + days - 1
                
                # Check if this city has fixed days
                if city in fixed_events:
                    required_start, required_end = fixed_events[city]
                    if not (current_day <= required_start and day_end >= required_end):
                        valid = False
                        break
                
                # Add to itinerary
                if days == 1:
                    day_str = f'Day {current_day}'
                else:
                    day_str = f'Day {current_day}-{day_end}'
                itinerary.append({'day_range': day_str, 'place': city})
                
                current_day = day_end + 1
                prev_city = city
            
            # Check if we used exactly 20 days
            if valid and current_day - 1 == total_days:
                # Verify all fixed events are properly placed
                fixed_ok = True
                for city, (start, end) in fixed_events.items():
                    found = False
                    for entry in itinerary:
                        if entry['place'] == city:
                            day_range = entry['day_range'][4:]  # Remove 'Day '
                            if '-' in day_range:
                                s, e = map(int, day_range.split('-'))
                                if s <= start and e >= end:
                                    found = True
                                    break
                            else:
                                day = int(day_range)
                                if day == start == end:
                                    found = True
                                    break
                    if not found:
                        fixed_ok = False
                        break
                
                if fixed_ok:
                    return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Run the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))