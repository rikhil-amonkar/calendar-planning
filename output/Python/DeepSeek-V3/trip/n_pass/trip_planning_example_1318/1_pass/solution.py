import json
from itertools import permutations

def main():
    # Cities and required days
    cities = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    # Direct flights (undirected graph)
    flights = {
        'Porto': ['Oslo', 'Edinburgh', 'Geneva'],
        'Oslo': ['Porto', 'Riga', 'Geneva', 'Edinburgh', 'Vilnius', 'Budapest', 'Helsinki', 'Tallinn'],
        'Edinburgh': ['Porto', 'Budapest', 'Geneva', 'Oslo', 'Helsinki', 'Riga'],
        'Budapest': ['Edinburgh', 'Geneva', 'Helsinki', 'Oslo'],
        'Geneva': ['Edinburgh', 'Budapest', 'Oslo', 'Porto', 'Helsinki'],
        'Riga': ['Oslo', 'Tallinn', 'Helsinki', 'Vilnius', 'Edinburgh'],
        'Tallinn': ['Riga', 'Vilnius', 'Helsinki', 'Oslo'],
        'Vilnius': ['Helsinki', 'Tallinn', 'Riga', 'Oslo'],
        'Helsinki': ['Vilnius', 'Tallinn', 'Riga', 'Oslo', 'Budapest', 'Geneva', 'Edinburgh']
    }
    
    # Constraints
    constraints = {
        'Oslo': {'day_range': (24, 25)},
        'Tallinn': {'day_range': (4, 8)}
    }
    
    # Generate all possible permutations of cities
    city_names = list(cities.keys())
    
    # We'll use a heuristic approach since full permutation is too large (9! = 362880)
    # Start with Tallinn (due to strict wedding constraint)
    # Then proceed to connected cities
    
    # Helper function to check if a path is valid
    def is_valid_path(path):
        # Check all cities are visited exactly once
        if sorted(path) != sorted(city_names):
            return False
        
        # Check flight connections
        for i in range(len(path)-1):
            if path[i+1] not in flights[path[i]]:
                return False
        
        return True
    
    # Find all valid paths starting with Tallinn (wedding constraint)
    valid_paths = []
    for perm in permutations(city_names):
        if perm[0] == 'Tallinn' and is_valid_path(perm):
            valid_paths.append(perm)
    
    # Now find a path that satisfies day constraints
    for path in valid_paths:
        day = 1
        itinerary = []
        valid = True
        
        for city in path:
            duration = cities[city]
            
            # Check constraints
            if city in constraints:
                start, end = constraints[city]['day_range']
                if city == 'Tallinn':
                    # Wedding must be between day 4-8
                    if not (day <= start and (day + duration - 1) >= end):
                        valid = False
                        break
                elif city == 'Oslo':
                    # Must be between day 24-25
                    if not (day <= 24 and (day + duration - 1) >= 25):
                        valid = False
                        break
            
            itinerary.append({
                'day_range': f"Day {day}-{day + duration - 1}",
                'place': city
            })
            day += duration
        
        if valid and day == 26:  # 25 days + 1 (since we increment at end)
            # Found valid itinerary
            output = {'itinerary': itinerary}
            print(json.dumps(output))
            return
    
    # If no valid path found (shouldn't happen with given constraints)
    print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()