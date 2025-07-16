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
        
        if current_day > total_days:
            return
        
        if not remaining_cities:
            if current_day - 1 == total_days:
                best_itinerary = current_itinerary.copy()
            return
        
        for city in remaining_cities:
            # Check if we can connect from previous city
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
            for (constraint_start, constraint_end) in cities[city]['constraints']:
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
            backtrack(current_itinerary, new_remaining, end_day + 1)
            
            # Backtrack
            current_itinerary.pop()
            
            if best_itinerary:
                return

    # Start with Tallinn first since it must include Day 1-2
    backtrack([], city_names, 1)
    
    return {'itinerary': best_itinerary} if best_itinerary else {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))