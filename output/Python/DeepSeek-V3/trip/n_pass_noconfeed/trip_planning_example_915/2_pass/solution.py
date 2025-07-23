import json
from itertools import permutations

def find_itinerary():
    # Define cities and their required days
    cities = {
        'Bucharest': 3,
        'Venice': 5,
        'Prague': 4,
        'Frankfurt': 5,
        'Zurich': 5,
        'Florence': 5,
        'Tallinn': 5
    }
    
    # Define direct flights as a graph
    flights = {
        'Prague': ['Tallinn', 'Zurich', 'Florence', 'Bucharest', 'Frankfurt'],
        'Tallinn': ['Prague', 'Frankfurt', 'Zurich'],
        'Zurich': ['Prague', 'Bucharest', 'Frankfurt', 'Venice', 'Florence'],
        'Florence': ['Prague', 'Frankfurt', 'Zurich'],
        'Frankfurt': ['Bucharest', 'Venice', 'Tallinn', 'Zurich', 'Prague', 'Florence'],
        'Bucharest': ['Frankfurt', 'Prague', 'Zurich'],
        'Venice': ['Frankfurt', 'Zurich']
    }
    
    # Fixed constraints - must be exactly within these ranges
    constraints = {
        'Venice': (22, 26),    # Days 22-26 (5 days)
        'Frankfurt': (12, 16),  # Days 12-16 (5 days)
        'Tallinn': (8, 12)      # Days 8-12 (5 days)
    }
    
    # These cities must be included in the itinerary
    required_cities = ['Venice', 'Frankfurt', 'Tallinn']
    
    # Generate all possible permutations of cities
    for perm in permutations(cities.keys()):
        # Check if all required cities are present
        if not all(city in perm for city in required_cities):
            continue
            
        # Check if the permutation satisfies flight connections
        valid_flights = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in flights[perm[i]]:
                valid_flights = False
                break
        if not valid_flights:
            continue
        
        # Assign days to each city in the permutation
        temp_itinerary = []
        current_day = 1
        for city in perm:
            days = cities[city]
            end_day = current_day + days - 1
            temp_itinerary.append((city, current_day, end_day))
            current_day = end_day + 1
        
        # Check if the total days match exactly 26
        if current_day - 1 != 26:
            continue
        
        # Check if constrained cities fall exactly in their required ranges
        meets_constraints = True
        for city, (req_start, req_end) in constraints.items():
            found = False
            for c, start, end in temp_itinerary:
                if c == city:
                    if start == req_start and end == req_end:
                        found = True
                        break
            if not found:
                meets_constraints = False
                break
        if not meets_constraints:
            continue
        
        # If all checks passed, format the itinerary
        itinerary = []
        for city, start, end in temp_itinerary:
            itinerary.append({
                'day_range': f"Day {start}-{end}",
                'place': city
            })
        return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))