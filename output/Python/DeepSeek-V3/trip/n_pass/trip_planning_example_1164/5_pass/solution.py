import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Reykjavik': {'days': 2, 'constraints': [(3, 4)]},
        'Stockholm': {'days': 2, 'constraints': [(4, 5)]},
        'Porto': {'days': 5, 'constraints': [(13, 17)]},
        'Nice': {'days': 3, 'constraints': []},
        'Venice': {'days': 4, 'constraints': []},
        'Vienna': {'days': 3, 'constraints': [(11, 13)]},
        'Split': {'days': 3, 'constraints': []},
        'Copenhagen': {'days': 2, 'constraints': []}
    }

    flight_routes = {
        'Copenhagen': ['Vienna', 'Split', 'Nice', 'Stockholm', 'Porto', 'Venice', 'Reykjavik'],
        'Nice': ['Stockholm', 'Reykjavik', 'Porto', 'Venice', 'Vienna', 'Copenhagen'],
        'Split': ['Copenhagen', 'Stockholm', 'Vienna'],
        'Reykjavik': ['Nice', 'Vienna', 'Copenhagen', 'Stockholm'],
        'Stockholm': ['Nice', 'Copenhagen', 'Split', 'Vienna', 'Reykjavik'],
        'Porto': ['Nice', 'Copenhagen', 'Vienna'],
        'Venice': ['Nice', 'Vienna', 'Copenhagen'],
        'Vienna': ['Copenhagen', 'Nice', 'Reykjavik', 'Stockholm', 'Venice', 'Split', 'Porto']
    }

    # Required cities that must be in the itinerary
    required_cities = ['Reykjavik', 'Stockholm', 'Vienna', 'Porto']
    
    # Optional cities that can be added to reach 17 days
    optional_cities = [city for city in cities if city not in required_cities]
    
    # Find combinations of optional cities that make total days = 17
    required_days = sum(cities[city]['days'] for city in required_cities)
    remaining_days = 17 - required_days
    
    # Find valid combinations of optional cities that sum to remaining_days
    valid_combinations = []
    for r in range(1, len(optional_cities)+1):
        for combo in combinations(optional_cities, r):
            if sum(cities[city]['days'] for city in combo) == remaining_days:
                valid_combinations.append(combo)
    
    # Try all permutations of required + optional cities
    for combo in valid_combinations:
        city_set = required_cities + list(combo)
        for perm in permutations(city_set):
            # Check flight connections
            valid = True
            for i in range(len(perm)-1):
                if perm[i+1] not in flight_routes[perm[i]]:
                    valid = False
                    break
            if not valid:
                continue
            
            # Check day constraints
            itinerary = []
            current_day = 1
            for city in perm:
                days = cities[city]['days']
                constraints = cities[city]['constraints']
                
                # Check if constraints are satisfied
                for (start, end) in constraints:
                    if not (current_day <= start and current_day + days - 1 >= end):
                        valid = False
                        break
                if not valid:
                    break
                
                itinerary.append((current_day, current_day + days - 1, city))
                current_day += days
            
            if valid and current_day - 1 == 17:
                # Format the result
                result = []
                for (start, end, city) in itinerary:
                    if start == end:
                        day_str = f"Day {start}"
                    else:
                        day_str = f"Day {start}-{end}"
                    result.append({"day_range": day_str, "place": city})
                return {"itinerary": result}
    
    return {"itinerary": []}

if __name__ == "__main__":
    itinerary = find_itinerary()
    print(json.dumps(itinerary, indent=2))