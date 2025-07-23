import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        'Venice': 3,
        'London': 3,
        'Lisbon': 4,
        'Brussels': 2,
        'Reykjavik': 3,
        'Santorini': 3,
        'Madrid': 5
    }
    
    # Direct flights
    flights = {
        'Venice': ['Madrid', 'Brussels', 'Santorini', 'Lisbon', 'London'],
        'Madrid': ['Venice', 'Reykjavik', 'London', 'Santorini', 'Lisbon', 'Brussels'],
        'Lisbon': ['Reykjavik', 'Venice', 'London', 'Madrid', 'Brussels'],
        'Brussels': ['Venice', 'London', 'Lisbon', 'Reykjavik', 'Madrid'],
        'Reykjavik': ['Lisbon', 'Madrid', 'London', 'Brussels'],
        'Santorini': ['Venice', 'London', 'Madrid'],
        'London': ['Brussels', 'Madrid', 'Santorini', 'Reykjavik', 'Lisbon', 'Venice']
    }
    
    # Fixed constraints
    fixed_constraints = [
        ('Brussels', 1, 2),    # Days 1-2
        ('Venice', 5, 7),      # Days 5-7
        ('Madrid', 8, 12)      # Days 8-12 (adjusted to not overlap with Venice)
    ]
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    
    # We'll try all possible permutations (though this is computationally expensive for larger numbers)
    for perm in permutations(city_names):
        itinerary = []
        valid = True
        
        # Initialize day assignments
        days_assigned = [False] * 18  # 1-based index up to day 17
        city_days_remaining = cities.copy()
        
        # Apply fixed constraints first
        for city, start, end in fixed_constraints:
            if city not in perm:
                valid = False
                break
            # Check if days are available
            for day in range(start, end + 1):
                if day > 17 or days_assigned[day]:
                    valid = False
                    break
            if not valid:
                break
            # Assign the days
            for day in range(start, end + 1):
                days_assigned[day] = True
            city_days_remaining[city] -= (end - start + 1)
            itinerary.append({'day_range': f'Day {start}-{end}', 'place': city})
        
        if not valid:
            continue
        
        # Now assign remaining cities
        prev_city = None
        current_day = 1
        
        # Find the first available day
        while current_day <= 17 and days_assigned[current_day]:
            current_day += 1
        
        for city in perm:
            if city_days_remaining[city] <= 0:
                continue
            
            # Find a block of consecutive days for this city
            days_needed = city_days_remaining[city]
            start_day = current_day
            end_day = start_day + days_needed - 1
            
            # Check if this block is available
            while end_day <= 17:
                available = True
                for day in range(start_day, end_day + 1):
                    if days_assigned[day]:
                        available = False
                        break
                if available:
                    break
                start_day += 1
                end_day += 1
            else:
                valid = False
                break
            
            # Check flight connection
            if prev_city and city not in flights[prev_city]:
                valid = False
                break
            
            # Assign the days
            for day in range(start_day, end_day + 1):
                days_assigned[day] = True
            itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
            city_days_remaining[city] = 0
            prev_city = city
            current_day = end_day + 1
            
            # Move to next available day
            while current_day <= 17 and days_assigned[current_day]:
                current_day += 1
        
        # Check if all cities are fully assigned
        if valid and all(days == 0 for days in city_days_remaining.values()):
            # Sort itinerary by day ranges
            def get_start_day(entry):
                return int(entry['day_range'].split('Day ')[1].split('-')[0])
            
            itinerary.sort(key=get_start_day)
            return {'itinerary': itinerary}
    
    # If no valid itinerary found
    return {'itinerary': []}

# Run the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))