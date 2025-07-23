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
    
    # Fixed constraints
    constraints = [
        ('Venice', (22, 26)),  # Wedding in Venice between day 22-26
        ('Frankfurt', (12, 16)),  # Annual show in Frankfurt between day 12-16
        ('Tallinn', (8, 12))  # Meet friends in Tallinn between day 8-12
    ]
    
    # Generate all possible permutations of cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if the permutation satisfies flight connections
        for i in range(len(perm) - 1):
            if perm[i+1] not in flights[perm[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Assign days to each city in the permutation
        temp_itinerary = []
        for city in perm:
            days = cities[city]
            temp_itinerary.append((city, current_day, current_day + days - 1))
            current_day += days
        
        # Check if the total days match 26
        if current_day - 1 != 26:
            continue
        
        # Check constraints
        meets_constraints = True
        for city, (start, end) in constraints:
            found = False
            for c, s, e in temp_itinerary:
                if c == city:
                    # Check if the city's days overlap with the constraint range
                    if not (e < start or s > end):
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