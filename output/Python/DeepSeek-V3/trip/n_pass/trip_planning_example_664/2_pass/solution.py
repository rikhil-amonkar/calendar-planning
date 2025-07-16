import json
from itertools import permutations

def find_itinerary():
    # Cities and their required stay durations
    cities = {
        'Tallinn': 2,
        'Bucharest': 4,
        'Seville': 5,
        'Stockholm': 5,
        'Munich': 5,
        'Milan': 2
    }
    
    # Flight connections (undirected)
    flight_graph = {
        'Milan': ['Stockholm', 'Munich', 'Seville'],
        'Stockholm': ['Milan', 'Munich', 'Tallinn'],
        'Munich': ['Milan', 'Stockholm', 'Bucharest', 'Seville', 'Tallinn'],
        'Bucharest': ['Munich'],
        'Seville': ['Munich', 'Milan'],
        'Tallinn': ['Stockholm', 'Munich']
    }
    
    # Constraints: (city, (start_day, end_day))
    constraints = [
        ('Bucharest', (1, 4)),  # Bucharest must include at least one day between day 1 and 4
        ('Munich', (4, 8)),      # Munich must include at least one day between day 4 and 8
        ('Seville', (8, 12))     # Seville must include at least one day between day 8 and 12
    ]
    
    # Generate all possible permutations of the cities
    city_list = list(cities.keys())
    
    for perm in permutations(city_list):
        # Check flight connections
        valid = True
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i+1]
            # Handle Munich/Munich spelling inconsistency
            if (current == 'Munich' and next_city not in flight_graph.get('Munich', [])) or \
               (next_city == 'Munich' and current not in flight_graph.get('Munich', [])):
                valid = False
                break
            if next_city not in flight_graph.get(current, []):
                valid = False
                break
        if not valid:
            continue
        
        # Build itinerary with days
        itinerary = []
        current_day = 1
        for city in perm:
            duration = cities[city]
            end_day = current_day + duration - 1
            itinerary.append((current_day, end_day, city))
            current_day = end_day + 1
        
        # Check total days
        if current_day - 1 != 18:
            continue
        
        # Check constraints
        meets_constraints = True
        for city, (start, end) in constraints:
            found = False
            for s, e, c in itinerary:
                if c == city:
                    # Check if city's stay overlaps with constraint range
                    if not (e < start or s > end):
                        found = True
                        break
            if not found:
                meets_constraints = False
                break
        
        if meets_constraints:
            # Format the itinerary
            formatted_itinerary = []
            for s, e, c in itinerary:
                if s == e:
                    day_range = f"Day {s}"
                else:
                    day_range = f"Day {s}-{e}"
                formatted_itinerary.append({"day_range": day_range, "place": c})
            return {"itinerary": formatted_itinerary}
    
    return {"itinerary": []}

# Run the function and print the result as JSON
result = find_itinerary()
print(json.dumps(result, indent=2))