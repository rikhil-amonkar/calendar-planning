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
        itinerary = []
        current_perm = list(perm)
        valid = True
        
        # Check if Helsinki is first (due to day 1-2 constraint)
        if current_perm[0] != 'Helsinki':
            continue
        
        # Try to build the itinerary
        day = 1
        prev_city = None
        total_days = 0
        
        for city in current_perm:
            req_days = cities[city]['days']
            constraint = cities[city]['constraint']
            
            # Check if the city can be visited within its constraint
            if constraint:
                start, end = constraint
                if not (day <= start and (day + req_days - 1) >= start) and not (day <= end and (day + req_days - 1) >= end):
                    if not (start >= day and end <= (day + req_days - 1)):
                        valid = False
                        break
            
            # Check flight connection
            if prev_city and city != prev_city:
                if city not in connections[prev_city]:
                    valid = False
                    break
                # Flight day counts for both cities
                itinerary[-1]['day_range'] = f"Day {day}-{day}"
                day += 1
                total_days += 1
                if total_days > 14:
                    valid = False
                    break
            
            # Add the city stay
            start_day = day
            end_day = day + req_days - 1
            itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': city
            })
            day += req_days
            total_days += req_days
            prev_city = city
            
            if total_days > 14:
                valid = False
                break
        
        if valid and total_days == 14:
            # Verify all constraints are met
            for entry in itinerary:
                place = entry['place']
                constraint = cities[place]['constraint']
                if constraint:
                    start, end = constraint
                    day_start = int(entry['day_range'].split('-')[0].split(' ')[1])
                    day_end = int(entry['day_range'].split('-')[1])
                    if not (day_start <= start <= day_end) or not (day_start <= end <= day_end):
                        valid = False
                        break
            if valid:
                return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Execute the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))