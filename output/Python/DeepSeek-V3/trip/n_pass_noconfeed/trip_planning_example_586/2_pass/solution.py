import json
from itertools import permutations

def find_itinerary():
    # Define the constraints
    total_days = 12
    city_days = {
        'Frankfurt': 3,
        'Naples': 4,
        'Helsinki': 4,
        'Lyon': 3,
        'Prague': 2
    }
    
    # Special constraints
    helsinki_show = (2, 5)  # Must be in Helsinki from Day 2 to Day 5 (4 days)
    prague_workshop = (1, 2)  # Must be in Prague on Day 1 and Day 2 (2 days)
    
    # Direct flights
    direct_flights = {
        'Prague': ['Lyon', 'Frankfurt', 'Helsinki'],
        'Lyon': ['Prague', 'Frankfurt'],
        'Frankfurt': ['Prague', 'Lyon', 'Helsinki', 'Naples'],
        'Helsinki': ['Prague', 'Frankfurt', 'Naples'],
        'Naples': ['Helsinki', 'Frankfurt']
    }
    
    # All cities
    cities = list(city_days.keys())
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        # Create a day-by-day plan
        plan = [None] * total_days  # Index 0 = Day 1, Index 11 = Day 12
        
        # First assign Prague (must be on days 1-2)
        try:
            plan[0] = 'Prague'  # Day 1
            plan[1] = 'Prague'  # Day 2
        except:
            continue
        
        # Then assign Helsinki (must be on days 2-5)
        # Note: Day 2 is already Prague, so we need to adjust
        # Since Day 2 is Prague, Helsinki must be days 3-6 to cover 4 days
        # But the constraint says "must be in Helsinki between day 2 to day 5"
        # So we interpret this as at least some days between 2-5 must be in Helsinki
        # Since we have 4 days in Helsinki, we'll do days 3-6 (but need to check if this satisfies)
        try:
            for day in range(2, 6):  # Days 3-6 (indices 2-5)
                plan[day] = 'Helsinki'
        except:
            continue
        
        # Now assign remaining days to other cities
        remaining_days = city_days.copy()
        remaining_days['Prague'] -= 2
        remaining_days['Helsinki'] -= 4
        
        # Check if we have negative remaining days (invalid)
        if any(v < 0 for v in remaining_days.values()):
            continue
        
        # Assign remaining cities
        current_city = None
        for day in range(total_days):
            if plan[day] is not None:
                current_city = plan[day]
                continue
            
            # Find next city to assign
            for city in perm:
                if city == current_city:
                    continue  # Can't stay in same city unless we have remaining days
                if remaining_days[city] <= 0:
                    continue
                if current_city and city not in direct_flights[current_city]:
                    continue
                
                # Assign as many consecutive days as possible
                max_days = min(remaining_days[city], total_days - day)
                for d in range(day, day + max_days):
                    if d >= total_days or plan[d] is not None:
                        break
                    plan[d] = city
                    remaining_days[city] -= 1
                current_city = city
                break
        
        # Check if all days are assigned and all city days are satisfied
        if None not in plan and all(v == 0 for v in remaining_days.values()):
            # Verify flight connections
            valid = True
            for i in range(1, total_days):
                prev_city = plan[i-1]
                current_city = plan[i]
                if prev_city != current_city and current_city not in direct_flights[prev_city]:
                    valid = False
                    break
            if valid:
                # Convert to itinerary format
                itinerary = []
                current_city = plan[0]
                start_day = 1
                for day in range(1, total_days):
                    if plan[day] != current_city:
                        itinerary.append({
                            'day_range': f'Day {start_day}-{day}',
                            'place': current_city
                        })
                        current_city = plan[day]
                        start_day = day + 1
                # Add last segment
                itinerary.append({
                    'day_range': f'Day {start_day}-{total_days}',
                    'place': current_city
                })
                return {'itinerary': itinerary}
    
    # If no valid itinerary found, return an empty list
    return {'itinerary': []}

# Execute the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))