import json
from itertools import permutations

def find_itinerary():
    # Input parameters
    total_days = 16
    city_days = {
        'Frankfurt': 4,
        'Manchester': 4,
        'Valencia': 4,
        'Naples': 4,
        'Oslo': 3,
        'Vilnius': 2
    }
    
    # Special constraints
    frankfurt_last_days = (13, 16)  # Day 13 to 16 in Frankfurt
    vilnius_wedding_days = (12, 13)  # Wedding between day 12 and 13
    
    # Flight connections
    connections = {
        'Valencia': ['Frankfurt', 'Naples'],
        'Manchester': ['Frankfurt', 'Naples', 'Oslo'],
        'Naples': ['Manchester', 'Frankfurt', 'Oslo', 'Valencia'],
        'Oslo': ['Naples', 'Frankfurt', 'Vilnius', 'Manchester'],
        'Vilnius': ['Frankfurt', 'Oslo'],
        'Frankfurt': ['Valencia', 'Manchester', 'Naples', 'Oslo', 'Vilnius']
    }
    
    # Generate all possible permutations of cities
    cities = list(city_days.keys())
    for perm in permutations(cities):
        itinerary = []
        current_perm = list(perm)
        
        # Check if Frankfurt is at the end (days 13-16)
        if current_perm[-1] != 'Frankfurt':
            continue
        
        # Check if Vilnius is visited around day 12-13
        day = 1
        vilnius_ok = False
        for city in current_perm:
            if city == 'Vilnius':
                if day <= vilnius_wedding_days[0] and day + city_days[city] - 1 >= vilnius_wedding_days[1]:
                    vilnius_ok = True
                    break
            day += city_days[city]
        if not vilnius_ok:
            continue
        
        # Check flight connections
        valid = True
        for i in range(len(current_perm) - 1):
            if current_perm[i+1] not in connections[current_perm[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Check total days
        total = sum(city_days[city] for city in current_perm)
        if total != total_days:
            continue
        
        # Build itinerary
        day = 1
        for i, city in enumerate(current_perm):
            stay_days = city_days[city]
            end_day = day + stay_days - 1
            
            # Add stay
            itinerary.append({
                'day_range': f'Day {day}-{end_day}',
                'place': city
            })
            
            # Add flight if not last city
            if i < len(current_perm) - 1:
                next_city = current_perm[i+1]
                itinerary.append({
                    'flying': f'Day {end_day}-{end_day}',
                    'from': city,
                    'to': next_city
                })
            
            day = end_day + 1
        
        # Check Frankfurt last days
        last_stay = itinerary[-2]  # Last stay is before last flight
        if last_stay['place'] == 'Frankfurt':
            start, end = map(int, last_stay['day_range'].replace('Day ', '').split('-'))
            if start <= frankfurt_last_days[0] and end >= frankfurt_last_days[1]:
                return itinerary
    
    return None

itinerary = find_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))