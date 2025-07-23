import json
from itertools import combinations

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
        ('Reykjavik', (1, 4)),      # Days 1-4
        ('Stuttgart', (4, 4)),      # Day 4 only
        ('Stuttgart', (7, 7)),      # Day 7 only
        ('Munich', (13, 15)),       # Days 13-15
        ('Istanbul', (19, 22))     # Days 19-22
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
            if day in schedule and schedule[day] != city:
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
    
    # Group consecutive available days into blocks
    day_blocks = []
    current_block = []
    
    for day in available_days:
        if not current_block or day == current_block[-1] + 1:
            current_block.append(day)
        else:
            day_blocks.append(current_block)
            current_block = [day]
    if current_block:
        day_blocks.append(current_block)
    
    # Assign cities to day blocks
    def assign_cities(blocks, cities_to_assign, prev_city=None):
        if not cities_to_assign:
            return True
            
        city, days_needed = cities_to_assign[0]
        
        # Try placing in each block
        for i, block in enumerate(blocks):
            if len(block) >= days_needed:
                # Check flight connection
                if prev_city and city not in direct_flights.get(prev_city, []):
                    continue
                
                # Try placing at start of block
                new_schedule = schedule.copy()
                for day in block[:days_needed]:
                    new_schedule[day] = city
                
                # Update blocks
                new_blocks = blocks.copy()
                remaining_days = block[days_needed:]
                if remaining_days:
                    new_blocks[i] = remaining_days
                else:
                    new_blocks.pop(i)
                
                # Recurse
                if assign_cities(new_blocks, cities_to_assign[1:], city):
                    schedule.update(new_schedule)
                    return True
                
        return False
    
    # Sort cities by days needed (descending) to place larger chunks first
    sorted_cities = sorted(remaining_cities.items(), key=lambda x: -x[1])
    
    if assign_cities(day_blocks, sorted_cities, prev_city=None):
        # Format the itinerary
        itinerary = []
        current_city = None
        start_day = 1
        
        for day in range(1, 26):
            city = schedule.get(day)
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