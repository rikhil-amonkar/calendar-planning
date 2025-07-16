import json

def find_itinerary():
    cities = {
        'Helsinki': {'days': 2, 'constraint': (1, 2)},
        'Warsaw': {'days': 3, 'constraint': (9, 11)},
        'Madrid': {'days': 4, 'constraint': None},
        'Split': {'days': 4, 'constraint': None},
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
    
    # Correct city name typos
    cities['Helsinki'] = cities.pop('Helsinki')
    cities['Madrid'] = cities.pop('Madrid')
    connections['Helsinki'] = connections.pop('Helsinki')
    connections['Madrid'] = connections.pop('Madrid')
    
    # Define possible city orders that might work
    possible_orders = [
        ['Helsinki', 'Reykjavik', 'Warsaw', 'Madrid', 'Split'],
        ['Helsinki', 'Reykjavik', 'Warsaw', 'Budapest', 'Madrid'],
        ['Helsinki', 'Split', 'Madrid', 'Warsaw', 'Reykjavik'],
        ['Helsinki', 'Budapest', 'Warsaw', 'Reykjavik', 'Madrid']
    ]
    
    for order in possible_orders:
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True
        
        for city in order:
            req_days = cities[city]['days']
            constraint = cities[city]['constraint']
            
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
        
        if valid and current_day - 1 == 14:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Execute and print result
result = find_itinerary()
print(json.dumps(result, indent=2))