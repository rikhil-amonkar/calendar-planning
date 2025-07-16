import json
from itertools import permutations

def find_itinerary():
    # Define the cities and their required days
    cities = {
        'Helsinki': {'days': 2, 'constraint': (1, 2)},
        'Warsaw': {'days': 3, 'constraint': (9, 11)},
        'Madrid': {'days': 4, 'constraint': None},
        'Split': {'days': 4, 'constraint': None},
        'Reykjavik': {'days': 2, 'constraint': (8, 9)},
        'Budapest': {'days': 4, 'constraint': None}
    }
    
    # Define the direct flight connections
    connections = {
        'Helsinki': ['Reykjavik', 'Split', 'Madrid', 'Budapest', 'Warsaw'],
        'Reykjavik': ['Helsinki', 'Warsaw', 'Budapest', 'Madrid'],
        'Budapest': ['Warsaw', 'Madrid', 'Reykjavik', 'Helsinki'],
        'Warsaw': ['Budapest', 'Reykjavik', 'Helsinki', 'Madrid', 'Split'],
        'Madrid': ['Split', 'Helsinki', 'Budapest', 'Warsaw'],
        'Split': ['Madrid', 'Helsinki', 'Warsaw']
    }
    
    # Generate all possible permutations of the cities
    city_names = list(cities.keys())
    for perm in permutations(city_names):
        # Must start with Helsinki (days 1-2)
        if perm[0] != 'Helsinki':
            continue
            
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True
        
        for city in perm:
            req_days = cities[city]['days']
            constraint = cities[city]['constraint']
            
            # Check if we have a flight day needed
            if prev_city and prev_city != city:
                # Check flight connection
                if city not in connections.get(prev_city, []):
                    valid = False
                    break
                # Flight takes a day
                current_day += 1
                if current_day > 14:
                    valid = False
                    break
            
            # Check city constraints
            if constraint:
                start, end = constraint
                city_start = current_day
                city_end = current_day + req_days - 1
                # Check if the constraint is fully covered by the stay
                if not (city_start <= start and end <= city_end):
                    valid = False
                    break
            
            # Add the city stay
            itinerary.append({
                'day_range': f"Day {current_day}-{current_day + req_days - 1}",
                'place': city
            })
            
            current_day += req_days
            prev_city = city
            
            if current_day > 14:
                valid = False
                break
        
        # Check if we exactly used 14 days
        if valid and current_day - 1 == 14:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Fix city name typos in the connections and cities dictionaries
def fix_city_names(data):
    if isinstance(data, dict):
        return {k.replace('Helsinki', 'Helsinki')
                   .replace('Madrid', 'Madrid')
                   .replace('Warsaw', 'Warsaw'): fix_city_names(v) 
                for k, v in data.items()}
    elif isinstance(data, list):
        return [fix_city_names(item) for item in data]
    else:
        return data.replace('Helsinki', 'Helsinki') if isinstance(data, str) else data

# Execute the function and print the result
result = find_itinerary()
fixed_result = fix_city_names(result)
print(json.dumps(fixed_result, indent=2))