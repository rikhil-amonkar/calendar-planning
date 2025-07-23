import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    # Special constraints
    conference_days = (20, 21)  # Madrid must be on these days
    stuttgart_friend_days = (1, 4)  # Stuttgart must include these days
    
    # Direct flights (bidirectional)
    flights = {
        'Helsinki': ['London', 'Madrid', 'Brussels', 'Split'],
        'Split': ['Madrid', 'Helsinki', 'London', 'Stuttgart'],
        'Madrid': ['Split', 'Helsinki', 'London', 'Mykonos', 'Bucharest', 'Brussels'],
        'London': ['Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Split', 'Mykonos', 'Stuttgart'],
        'Brussels': ['London', 'Bucharest', 'Helsinki', 'Madrid'],
        'Bucharest': ['London', 'Brussels', 'Madrid'],
        'Mykonos': ['Madrid', 'London'],
        'Stuttgart': ['London', 'Split']
    }
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    
    # We'll try all permutations but with some optimizations
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        # Calculate day ranges for each city in this permutation
        day_ranges = {}
        for city in perm:
            end_day = current_day + cities[city] - 1
            day_ranges[city] = (current_day, end_day)
            current_day = end_day + 1
        
        # Check total days (must be exactly 21)
        if current_day - 1 != 21:
            continue
        
        # Check Madrid constraint (must be on days 20-21)
        madrid_start, madrid_end = day_ranges['Madrid']
        if not (madrid_start <= conference_days[0] and madrid_end >= conference_days[1]):
            continue
        
        # Check Stuttgart constraint (must include days 1-4)
        stuttgart_start, stuttgart_end = day_ranges['Stuttgart']
        if not (stuttgart_start <= stuttgart_friend_days[1] and 
                stuttgart_end >= stuttgart_friend_days[0]):
            continue
        
        # Check flight connections
        for i in range(len(perm)-1):
            current_city = perm[i]
            next_city = perm[i+1]
            if next_city not in flights[current_city]:
                valid = False
                break
        
        if not valid:
            continue
        
        # If we get here, we have a valid itinerary
        for city in perm:
            start, end = day_ranges[city]
            itinerary.append({
                'day_range': f"Day {start}-{end}",
                'place': city
            })
        
        return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Execute and print result
result = find_itinerary()
print(json.dumps(result, indent=2))