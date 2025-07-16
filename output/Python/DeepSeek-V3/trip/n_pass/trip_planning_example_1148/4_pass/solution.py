import json

def find_itinerary():
    cities = {
        'Lisbon': {'duration': 2, 'constraints': [(4, 5)]},
        'Dubrovnik': {'duration': 5, 'constraints': []},
        'Copenhagen': {'duration': 5, 'constraints': []},
        'Prague': {'duration': 3, 'constraints': []},
        'Tallinn': {'duration': 2, 'constraints': [(1, 2)]},
        'Stockholm': {'duration': 4, 'constraints': [(13, 16)]},
        'Split': {'duration': 3, 'constraints': []},
        'Lyon': {'duration': 2, 'constraints': [(18, 19)]}
    }

    flight_connections = {
        'Dubrovnik': ['Stockholm', 'Copenhagen'],
        'Lisbon': ['Copenhagen', 'Lyon', 'Stockholm', 'Prague'],
        'Copenhagen': ['Lisbon', 'Stockholm', 'Split', 'Dubrovnik', 'Prague', 'Tallinn'],
        'Prague': ['Stockholm', 'Lyon', 'Lisbon', 'Split', 'Copenhagen', 'Tallinn'],
        'Tallinn': ['Stockholm', 'Copenhagen', 'Prague'],
        'Stockholm': ['Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Lisbon', 'Split'],
        'Split': ['Copenhagen', 'Stockholm', 'Lyon', 'Prague'],
        'Lyon': ['Lisbon', 'Prague', 'Split']
    }

    total_days = 19
    city_names = list(cities.keys())
    best_itinerary = []

    def backtrack(current_itinerary, remaining_cities, current_day):
        nonlocal best_itinerary
        
        # If we've used exactly 19 days and visited all cities
        if current_day - 1 == total_days and not remaining_cities:
            best_itinerary = current_itinerary.copy()
            return True
        
        # If we've exceeded days or have no solution path
        if current_day > total_days or (not remaining_cities and current_day - 1 < total_days):
            return False
        
        # Try all remaining cities
        for city in remaining_cities:
            # Check flight connection if not first city
            if current_itinerary:
                last_city = current_itinerary[-1]['place']
                if city not in flight_connections[last_city]:
                    continue
            
            duration = cities[city]['duration']
            start_day = current_day
            end_day = current_day + duration - 1
            
            # Check if exceeds total days
            if end_day > total_days:
                continue
            
            # Check city constraints
            valid = True
            constraints = cities[city].get('constraints', []) + cities[city].get('constraints', [])
            for (constraint_start, constraint_end) in constraints:
                if not (start_day <= constraint_start and constraint_end <= end_day):
                    valid = False
                    break
            if not valid:
                continue
            
            # Add to itinerary
            current_itinerary.append({
                'day_range': f'Day {start_day}-{end_day}',
                'place': city
            })
            
            new_remaining = [c for c in remaining_cities if c != city]
            
            # Recurse
            if backtrack(current_itinerary, new_remaining, end_day + 1):
                return True
                
            # Backtrack
            current_itinerary.pop()
        
        return False

    # Start with Tallinn first since it must include Day 1-2
    remaining = [c for c in city_names if c != 'Tallinn']
    backtrack([{
        'day_range': 'Day 1-2',
        'place': 'Tallinn'
    }], remaining, 3)
    
    return {'itinerary': best_itinerary} if best_itinerary else {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))