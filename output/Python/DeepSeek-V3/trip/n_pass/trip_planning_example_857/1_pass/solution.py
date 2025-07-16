import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        "Porto": 2,
        "Geneva": 3,
        "Mykonos": 3,
        "Manchester": 4,
        "Hamburg": 5,
        "Naples": 5,
        "Frankfurt": 2
    }
    
    # Direct flights
    direct_flights = {
        "Hamburg": ["Frankfurt", "Porto", "Geneva", "Manchester"],
        "Frankfurt": ["Hamburg", "Geneva", "Porto", "Naples", "Manchester"],
        "Geneva": ["Hamburg", "Mykonos", "Frankfurt", "Porto", "Manchester", "Naples"],
        "Mykonos": ["Geneva", "Naples"],
        "Naples": ["Mykonos", "Manchester", "Frankfurt", "Geneva"],
        "Porto": ["Hamburg", "Frankfurt", "Geneva", "Manchester"],
        "Manchester": ["Geneva", "Naples", "Frankfurt", "Porto", "Hamburg"]
    }
    
    # Constraints
    constraints = [
        ("Porto", 2),
        ("Geneva", 3),
        ("Mykonos", 3, (10, 12)),
        ("Manchester", 4, (15, 18)),
        ("Hamburg", 5),
        ("Naples", 5),
        ("Frankfurt", 2, (5, 6))
    ]
    
    # Generate all possible permutations of cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if permutation satisfies all constraints
        for city in perm:
            # Find the constraint for the current city
            constraint = next((c for c in constraints if c[0] == city), None)
            if not constraint:
                valid = False
                break
            
            days = constraint[1]
            day_range = None
            
            # Check if there's a specific day range for the city
            if len(constraint) > 2:
                start, end = constraint[2]
                if current_day > start or current_day + days - 1 > end:
                    valid = False
                    break
                day_range = f"Day {current_day}-{current_day + days - 1}"
            else:
                day_range = f"Day {current_day}-{current_day + days - 1}"
            
            itinerary.append({"day_range": day_range, "place": city})
            current_day += days
            
            # Check if we've exceeded the total days
            if current_day > 18:
                valid = False
                break
        
        if valid and current_day == 19:  # 18 days + 1 (since we increment after adding)
            # Check flight connections
            for i in range(len(itinerary) - 1):
                current_city = itinerary[i]["place"]
                next_city = itinerary[i+1]["place"]
                if next_city not in direct_flights.get(current_city, []):
                    valid = False
                    break
            
            if valid:
                return {"itinerary": itinerary}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result))