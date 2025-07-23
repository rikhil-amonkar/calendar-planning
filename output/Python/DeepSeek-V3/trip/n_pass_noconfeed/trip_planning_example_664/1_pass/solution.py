import json
from itertools import permutations

def find_itinerary():
    # Cities and their required stay durations
    cities = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2
    }
    
    # Direct flights between cities
    direct_flights = {
        "Milan": ["Stockholm", "Munich", "Seville"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Munich": ["Milan", "Stockholm", "Bucharest", "Seville", "Tallinn"],
        "Bucharest": ["Munich"],
        "Seville": ["Munich", "Milan"],
        "Tallinn": ["Stockholm", "Munich"]
    }
    
    # Constraints
    constraints = [
        ("Bucharest", (1, 4)),
        ("Seville", (8, 12)),
        ("Munich", (4, 8))
    ]
    
    # Generate all possible permutations of cities
    city_names = list(cities.keys())
    for perm in permutations(city_names):
        # Check if the permutation satisfies the flight constraints
        valid = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in direct_flights.get(perm[i], []):
                valid = False
                break
        if not valid:
            continue
        
        # Try to assign days to the permutation
        itinerary = []
        current_day = 1
        remaining_days = {city: cities[city] for city in cities}
        
        for city in perm:
            duration = remaining_days[city]
            end_day = current_day + duration - 1
            itinerary.append((current_day, end_day, city))
            current_day = end_day + 1
        
        # Check if the total days match
        if current_day - 1 != 18:
            continue
        
        # Check constraints
        meets_constraints = True
        for city, (start, end) in constraints:
            found = False
            for (s, e, c) in itinerary:
                if c == city and s <= end and e >= start:
                    found = True
                    break
            if not found:
                meets_constraints = False
                break
        if meets_constraints:
            # Format the itinerary
            formatted_itinerary = []
            for (s, e, c) in itinerary:
                if s == e:
                    day_range = f"Day {s}"
                else:
                    day_range = f"Day {s}-{e}"
                formatted_itinerary.append({"day_range": day_range, "place": c})
            return {"itinerary": formatted_itinerary}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))