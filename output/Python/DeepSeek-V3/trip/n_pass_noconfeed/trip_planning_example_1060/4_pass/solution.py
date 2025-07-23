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
    
    # Direct flights (bidirectional)
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
    
    # Calculate total remaining days needed
    total_needed = sum(remaining_cities.values())
    total_available = len(available_days)
    
    if total_needed > total_available:
        return {'itinerary': []}
    
    # Try with a more guided approach
    def backtrack(current_schedule, remaining_days_list, remaining_cities, prev_city):
        if not remaining_cities:
            # All cities placed, check flight connections
            return current_schedule
        
        for city in list(remaining_cities.keys()):
            days_needed = remaining_cities[city]
            
            # Check if we can connect from previous city
            if prev_city and city not in direct_flights.get(prev_city, []):
                continue
                
            # Try placing this city in all possible positions
            for i in range(len(remaining_days_list) - days_needed + 1):
                start = remaining_days_list[i]
                end = start + days_needed - 1
                
                # Check if consecutive days are available
                if all(day in remaining_days_list for day in range(start, end + 1)):
                    new_schedule = current_schedule.copy()
                    new_remaining_days = remaining_days_list.copy()
                    
                    # Place the city
                    for day in range(start, end + 1):
                        new_schedule[day] = city
                        new_remaining_days.remove(day)
                    
                    new_remaining_cities = remaining_cities.copy()
                    del new_remaining_cities[city]
                    
                    result = backtrack(new_schedule, new_remaining_days, new_remaining_cities, city)
                    if result:
                        return result
        return None
    
    final_schedule = backtrack(schedule.copy(), available_days.copy(), remaining_cities.copy(), None)
    
    if not final_schedule:
        return {'itinerary': []}
    
    # Format the itinerary
    itinerary = []
    current_city = None
    start_day = 1
    
    for day in range(1, 26):
        city = final_schedule.get(day)
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

result = find_itinerary()
print(json.dumps(result, indent=2))