import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Helsinki': {'days': 2, 'constraint': (1, 2)},
        'Warsaw': {'days': 3, 'constraint': (9, 11)},
        'Madrid': {'days': 4, 'constraint': None},
        'Split': {'days': 4, 'constraint': None},  # Fixed typo in 'constraint'
        'Reykjavik': {'days': 2, 'constraint': (8, 9)},
        'Budapest': {'days': 4, 'constraint': None}
    }
    
    connections = {
        'Helsinki': ['Reykjavik', 'Split', 'Madrid', 'Budapest', 'Warsaw'],
        'Reykjavik': ['Helsinki', 'Warsaw', 'Budapest', 'Madrid'],
        'Budapest': ['Warsaw', 'Madrid', 'Reykjavik', 'Helsinki'],
        'Warsaw': ['Budapest', 'Reykjavik', 'Helsinki', 'Madrid', 'Split'],
        'Madrid': ['Split', 'Helsinki', 'Budapest', 'Warsaw'],
        'Split': ['Madrid', 'Helsinki', 'Warsaw']
    }
    
    # We'll try different city orders that might satisfy the constraints
    # Since permutations would be too many, we'll try likely candidates
    city_names = list(cities.keys())
    possible_orders = [
        ['Helsinki', 'Reykjavik', 'Warsaw', 'Madrid', 'Split'],
        ['Helsinki', 'Reykjavik', 'Warsaw', 'Budapest'],
        ['Helsinki', 'Split', 'Madrid', 'Warsaw', 'Reykjavik'],
        ['Helsinki', 'Budapest', 'Warsaw', 'Reykjavik'],
        ['Helsinki', 'Reykjavik', 'Budapest', 'Warsaw'],
        ['Helsinki', 'Madrid', 'Split', 'Warsaw']
    ]
    
    for order in possible_orders:
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True
        
        for city in order:
            city_data = cities[city]
            req_days = city_data['days']
            constraint = city_data['constraint']
            
            # Check flight connection if needed
            if prev_city and prev_city != city:
                if city not in connections.get(prev_city, []):
                    valid = False
                    break
                current_day += 1  # Flight day
                if current_day > 14:
                    valid = False
                    break
            
            # Check city constraints
            if constraint:
                start, end = constraint
                city_start = current_day
                city_end = current_day + req_days - 1
                if not (city_start <= start and end <= city_end):
                    valid = False
                    break
            
            # Add city stay
            itinerary.append({
                'day_range': f"Day {current_day}-{current_day + req_days - 1}",
                'place': city
            })
            
            current_day += req_days
            prev_city = city
            
            if current_day > 14:
                valid = False
                break
        
        # Check if we exactly filled 14 days
        if valid and (current_day - 1) == 14:
            return {'itinerary': itinerary}
    
    # If no valid itinerary found, return empty
    return {'itinerary': []}

# Execute and print result
result = find_itinerary()
print(json.dumps(result, indent=2))