import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4
    }
    
    # Direct flights (from -> to)
    flights = {
        "Helsinki": ["Prague", "Reykjavik", "Dubrovnik"],
        "Prague": ["Helsinki", "Valencia", "Reykjavik"],
        "Valencia": ["Prague", "Porto"],
        "Porto": ["Valencia"],
        "Reykjavik": ["Helsinki", "Prague"],
        "Dubrovnik": ["Helsinki"]
    }
    
    # Porto must be between day 16-18 (inclusive)
    porto_constraint = (16, 18)
    
    # Generate all possible permutations of cities
    for perm in permutations(cities.keys()):
        # Check if Porto is in the permutation
        if "Porto" not in perm:
            continue
            
        # Find Porto's position in the permutation
        porto_index = perm.index("Porto")
        
        # Check flight connections
        valid = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in flights[perm[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Assign days and check constraints
        itinerary = []
        current_day = 1
        remaining_cities = cities.copy()
        
        for city in perm:
            days_needed = remaining_cities[city]
            end_day = current_day + days_needed - 1
            
            # Check if Porto is within its constraint
            if city == "Porto":
                if not (porto_constraint[0] <= current_day and end_day <= porto_constraint[1]):
                    valid = False
                    break
            
            # Check total days don't exceed 18
            if end_day > 18:
                valid = False
                break
            
            itinerary.append({
                "day_range": f"Day {current_day}-{end_day}",
                "place": city
            })
            current_day = end_day + 1
            del remaining_cities[city]
        
        # Check all cities are visited and total days are exactly 18
        if valid and not remaining_cities and current_day == 19:
            return {"itinerary": itinerary}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))