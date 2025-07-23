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
    
    # Constraints (city: (min_day, max_day))
    constraints = {
        "Bucharest": (1, 4),    # Must visit between day 1-4
        "Seville": (8, 12),     # Must visit between day 8-12
        "Munich": (4, 8)        # Must visit between day 4-8
    }
    
    # Generate all possible permutations of cities
    for perm in permutations(cities.keys()):
        # Check flight connections
        valid_flights = True
        for i in range(len(perm)-1):
            if perm[i+1] not in direct_flights.get(perm[i], []):
                valid_flights = False
                break
        if not valid_flights:
            continue
        
        # Assign days to the itinerary
        itinerary = []
        current_day = 1
        total_days = 0
        
        for city in perm:
            duration = cities[city]
            end_day = current_day + duration - 1
            itinerary.append((current_day, end_day, city))
            current_day = end_day + 1
            total_days += duration
        
        # Check total days <= 18
        if total_days > 18:
            continue
        
        # Check constraints
        meets_constraints = True
        for city, (min_day, max_day) in constraints.items():
            city_found = False
            for start, end, c in itinerary:
                if c == city:
                    # Check if any day in the stay is within the constraint window
                    if not (end < min_day or start > max_day):
                        city_found = True
                        break
            if not city_found:
                meets_constraints = False
                break
        
        if meets_constraints:
            # Format the output
            formatted = []
            for start, end, city in itinerary:
                if start == end:
                    day_str = f"Day {start}"
                else:
                    day_str = f"Day {start}-{end}"
                formatted.append({"day_range": day_str, "place": city})
            return {"itinerary": formatted}
    
    return {"itinerary": []}

# Fixed city name spellings
result = find_itinerary()
print(json.dumps(result, indent=2))