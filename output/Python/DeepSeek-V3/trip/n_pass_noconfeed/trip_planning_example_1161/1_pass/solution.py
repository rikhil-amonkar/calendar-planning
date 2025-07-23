import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    city_days = {
        'Mykonos': 4,
        'Krakow': 5,
        'Vilnius': 2,
        'Helsinki': 2,
        'Dubrovnik': 3,
        'Oslo': 2,
        'Madrid': 5,
        'Paris': 2
    }
    
    # Fixed constraints
    fixed_constraints = [
        ('Mykonos', (15, 18)),
        ('Dubrovnik', (2, 4)),
        ('Oslo', (1, 2))
    ]
    
    # Direct flights
    direct_flights = {
        'Oslo': ['Krakow', 'Paris', 'Madrid', 'Helsinki', 'Dubrovnik', 'Vilnius'],
        'Krakow': ['Oslo', 'Paris', 'Vilnius', 'Helsinki'],
        'Paris': ['Oslo', 'Madrid', 'Krakow', 'Helsinki', 'Vilnius'],
        'Madrid': ['Paris', 'Dubrovnik', 'Mykonos', 'Oslo', 'Helsinki'],
        'Helsinki': ['Vilnius', 'Oslo', 'Krakow', 'Dubrovnik', 'Paris', 'Madrid'],
        'Dubrovnik': ['Helsinki', 'Madrid', 'Oslo'],
        'Vilnius': ['Helsinki', 'Oslo', 'Krakow', 'Paris'],
        'Mykonos': ['Madrid']
    }
    
    # All cities
    cities = list(city_days.keys())
    
    # Generate all possible permutations of cities
    for perm in permutations(cities):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check fixed constraints first
        for city, (start, end) in fixed_constraints:
            if city not in perm:
                valid = False
                break
        
        if not valid:
            continue
        
        # Try to build itinerary
        prev_city = None
        remaining_days = city_days.copy()
        
        for city in perm:
            if remaining_days[city] <= 0:
                continue
            
            # Check if city has fixed constraints
            fixed = False
            for fc, (start, end) in fixed_constraints:
                if fc == city:
                    fixed = True
                    days_needed = end - start + 1
                    if remaining_days[city] != days_needed:
                        valid = False
                        break
                    if current_day > start or current_day + days_needed - 1 > end:
                        valid = False
                        break
                    itinerary.append({
                        'day_range': f"Day {start}-{end}",
                        'place': city
                    })
                    remaining_days[city] = 0
                    current_day = end + 1
                    prev_city = city
                    break
            if not valid:
                break
            if fixed:
                continue
            
            # Non-fixed city
            days_needed = remaining_days[city]
            end_day = current_day + days_needed - 1
            
            # Check flight connection
            if prev_city is not None:
                if city not in direct_flights.get(prev_city, []):
                    valid = False
                    break
            
            itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            remaining_days[city] = 0
            prev_city = city
            current_day = end_day + 1
        
        # Check if all days are covered and all cities visited
        if valid and current_day <= 18:
            continue
        if valid and all(v == 0 for v in remaining_days.values()):
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Run the function and print the result
print(json.dumps(find_itinerary()))