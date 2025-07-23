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
    
    # Initialize schedule
    schedule = {}
    fixed_cities = set()
    
    # Apply fixed constraints
    for city, (start, end) in fixed_constraints:
        for day in range(start, end + 1):
            if day in schedule:
                return {'itinerary': []}  # Conflict in fixed constraints
            schedule[day] = city
        fixed_cities.add(city)
    
    # Remaining cities to schedule
    remaining_cities = {city: days for city, days in cities.items() if city not in fixed_cities}
    
    # Available day slots (1-25, excluding fixed days)
    all_days = set(range(1, 26))
    fixed_days = set(schedule.keys())
    available_days = sorted(all_days - fixed_days)
    
    # Try all possible city orders and placements
    for city_order in permutations(remaining_cities.keys()):
        temp_schedule = schedule.copy()
        remaining_days = available_days.copy()
        valid = True
        
        for city in city_order:
            days_needed = remaining_cities[city]
            # Try to place the city in the earliest possible consecutive block
            placed = False
            for i in range(len(remaining_days) - days_needed + 1):
                start = remaining_days[i]
                end = start + days_needed - 1
                # Check if consecutive days are available
                if all(day in remaining_days for day in range(start, end + 1)):
                    # Place the city
                    for day in range(start, end + 1):
                        temp_schedule[day] = city
                        remaining_days.remove(day)
                    placed = True
                    break
            if not placed:
                valid = False
                break
        
        if not valid:
            continue
        
        # Check flight connections
        prev_city = None
        flight_days = sorted(temp_schedule.keys())
        for day in flight_days:
            city = temp_schedule[day]
            if prev_city is None:
                prev_city = city
                continue
            if city != prev_city:
                if city not in direct_flights.get(prev_city, []):
                    valid = False
                    break
                prev_city = city
        
        if valid:
            # Format the itinerary
            itinerary = []
            current_city = None
            start_day = None
            for day in range(1, 26):
                city = temp_schedule.get(day)
                if city != current_city:
                    if current_city is not None:
                        itinerary.append({
                            'day_range': f'Day {start_day}-{day-1}',
                            'place': current_city
                        })
                    current_city = city
                    start_day = day
            # Add the last segment
            if current_city is not None:
                itinerary.append({
                    'day_range': f'Day {start_day}-25',
                    'place': current_city
                })
            
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))