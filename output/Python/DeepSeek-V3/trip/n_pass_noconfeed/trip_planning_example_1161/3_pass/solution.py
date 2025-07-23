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
    
    # Fixed constraints (city: (start_day, end_day))
    fixed_constraints = {
        'Mykonos': (15, 18),  # Days 15-18 (4 days)
        'Dubrovnik': (2, 4),   # Days 2-4 (3 days)
        'Oslo': (1, 2)        # Days 1-2 (2 days)
    }
    
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
    
    # All cities except fixed ones
    flexible_cities = [city for city in city_days if city not in fixed_constraints]
    
    # Generate all possible permutations of flexible cities
    for perm in permutations(flexible_cities):
        day_plan = [None] * 18  # 1-based indexing (days 1-18)
        remaining_days = city_days.copy()
        valid = True
        
        # Place fixed cities first
        for city, (start, end) in fixed_constraints.items():
            days_needed = end - start + 1
            if remaining_days[city] != days_needed:
                valid = False
                break
            for day in range(start-1, end):  # Convert to 0-based index
                day_plan[day] = city
            remaining_days[city] = 0
        
        if not valid:
            continue
        
        # Try to place flexible cities
        current_day = 0
        prev_city = None
        
        for city in perm:
            if remaining_days[city] <= 0:
                continue
            
            days_needed = remaining_days[city]
            found_spot = False
            
            # Try to find a spot for this city
            for start_day in range(18 - days_needed + 1):
                end_day = start_day + days_needed
                
                # Check if all days in range are available
                if any(day_plan[d] is not None for d in range(start_day, end_day)):
                    continue
                
                # Check flight connection constraints
                # Find the previous city (if any) before this spot
                prev_city_before = None
                for d in range(start_day-1, -1, -1):
                    if day_plan[d] is not None:
                        prev_city_before = day_plan[d]
                        break
                
                # Find the next city (if any) after this spot
                next_city_after = None
                for d in range(end_day, 18):
                    if day_plan[d] is not None:
                        next_city_after = day_plan[d]
                        break
                
                # Check flight connections
                valid_connection = True
                if prev_city_before is not None and city not in direct_flights.get(prev_city_before, []):
                    valid_connection = False
                if next_city_after is not None and next_city_after not in direct_flights.get(city, []):
                    valid_connection = False
                
                if not valid_connection:
                    continue
                
                # Place the city
                for d in range(start_day, end_day):
                    day_plan[d] = city
                remaining_days[city] = 0
                found_spot = True
                break
            
            if not found_spot:
                valid = False
                break
        
        # Check if all cities are placed
        if valid and all(v == 0 for v in remaining_days.values()):
            # Convert day plan to itinerary format
            itinerary = []
            current_city = None
            start_day = 0
            
            for day in range(18):
                if day_plan[day] != current_city:
                    if current_city is not None:
                        itinerary.append({
                            'day_range': f"Day {start_day+1}-{day}",
                            'place': current_city
                        })
                    current_city = day_plan[day]
                    start_day = day
            
            # Add the last segment
            if current_city is not None:
                itinerary.append({
                    'day_range': f"Day {start_day+1}-18",
                    'place': current_city
                })
            
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

# Run the function and print the result
print(json.dumps(find_itinerary()))