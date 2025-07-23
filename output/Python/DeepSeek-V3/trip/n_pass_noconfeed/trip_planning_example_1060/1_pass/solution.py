import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        'Stuttgart': 4,
        'Istanbul': 4,
        'Vilnius': 4,
        'Seville': 3,
        'Geneva': 5,
        'Valencia': 5,
        'Munich': 3,
        'Reykjavik': 4
    }
    
    # Fixed constraints
    fixed_constraints = [
        ('Reykjavik', (1, 4)),
        ('Stuttgart', (4, 4)),
        ('Stuttgart', (7, 7)),
        ('Munich', (13, 15)),
        ('Istanbul', (19, 22))
    ]
    
    # Direct flights
    direct_flights = {
        'Geneva': ['Istanbul', 'Munich', 'Valencia'],
        'Istanbul': ['Geneva', 'Stuttgart', 'Valencia', 'Vilnius', 'Munich'],
        'Reykjavik': ['Munich', 'Stuttgart'],
        'Stuttgart': ['Valencia', 'Istanbul', 'Reykjavik'],
        'Munich': ['Reykjavik', 'Geneva', 'Vilnius', 'Seville', 'Istanbul', 'Valencia'],
        'Valencia': ['Stuttgart', 'Seville', 'Istanbul', 'Geneva', 'Munich'],
        'Seville': ['Valencia', 'Munich'],
        'Vilnius': ['Istanbul', 'Munich']
    }
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    # Check each permutation for validity
    for order in possible_orders:
        itinerary = []
        current_city = None
        day = 1
        valid = True
        
        # Assign fixed constraints first
        fixed_days = {}
        for city, (start, end) in fixed_constraints:
            for d in range(start, end + 1):
                if d in fixed_days:
                    valid = False
                    break
                fixed_days[d] = city
            if not valid:
                break
        
        if not valid:
            continue
        
        # Assign remaining days
        remaining_days = cities.copy()
        for city in order:
            if city in remaining_days:
                days_needed = remaining_days[city]
                start_day = day
                end_day = day + days_needed - 1
                
                # Check if any fixed day conflicts
                for d in range(start_day, end_day + 1):
                    if d in fixed_days:
                        valid = False
                        break
                if not valid:
                    break
                
                # Assign days
                for d in range(start_day, end_day + 1):
                    if d > 25:
                        valid = False
                        break
                    fixed_days[d] = city
                if not valid:
                    break
                
                day = end_day + 1
                del remaining_days[city]
        
        if not valid or remaining_days:
            continue
        
        # Check flight connections
        prev_city = None
        flight_days = sorted(fixed_days.keys())
        for d in flight_days:
            city = fixed_days[d]
            if prev_city is None:
                prev_city = city
                continue
            if city != prev_city:
                if city not in direct_flights.get(prev_city, []):
                    valid = False
                    break
                prev_city = city
        
        if valid:
            # Group consecutive days
            itinerary = []
            current_city = None
            start_day = None
            for d in range(1, 26):
                city = fixed_days[d]
                if city != current_city:
                    if current_city is not None:
                        itinerary.append({
                            'day_range': f'Day {start_day}-{d-1}',
                            'place': current_city
                        })
                    current_city = city
                    start_day = d
            itinerary.append({
                'day_range': f'Day {start_day}-25',
                'place': current_city
            })
            
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))