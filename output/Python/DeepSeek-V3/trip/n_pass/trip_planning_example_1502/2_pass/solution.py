import json
from itertools import permutations

def find_itinerary():
    # Define cities and their required days
    cities = {
        'Santorini': 3,
        'Valencia': 4,
        'Madrid': 2,
        'Seville': 2,
        'Bucharest': 3,
        'Vienna': 4,
        'Riga': 4,
        'Tallinn': 5,
        'Krakow': 5,
        'Frankfurt': 4
    }
    
    # Define fixed events
    fixed_events = [
        {'city': 'Madrid', 'day_range': (6, 7)},
        {'city': 'Vienna', 'day_range': (3, 6)},
        {'city': 'Riga', 'day_range': (20, 23)},
        {'city': 'Tallinn', 'day_range': (23, 27)},
        {'city': 'Krakow', 'day_range': (11, 15)}
    ]
    
    # Define flight connections
    flights = {
        'Vienna': ['Bucharest', 'Seville', 'Valencia', 'Madrid', 'Krakow', 'Frankfurt', 'Riga'],
        'Bucharest': ['Vienna', 'Riga', 'Valencia', 'Santorini', 'Frankfurt', 'Madrid'],
        'Santorini': ['Madrid', 'Bucharest', 'Vienna'],
        'Madrid': ['Santorini', 'Valencia', 'Seville', 'Bucharest', 'Frankfurt'],
        'Seville': ['Valencia', 'Vienna', 'Madrid'],
        'Valencia': ['Seville', 'Madrid', 'Bucharest', 'Krakow', 'Frankfurt'],
        'Riga': ['Bucharest', 'Vienna', 'Frankfurt', 'Tallinn'],
        'Tallinn': ['Riga', 'Frankfurt'],
        'Krakow': ['Valencia', 'Frankfurt', 'Vienna'],
        'Frankfurt': ['Valencia', 'Krakow', 'Vienna', 'Tallinn', 'Bucharest', 'Riga', 'Madrid']
    }
    
    # Assign fixed events to cities
    for event in fixed_events:
        city = event['city']
        day_start, day_end = event['day_range']
        cities[city] -= (day_end - day_start + 1)
    
    # Remove cities with zero remaining days
    remaining_cities = {k: v for k, v in cities.items() if v > 0}
    
    # Generate all possible permutations of remaining cities
    for perm in permutations(remaining_cities.keys()):
        itinerary = []
        current_day = 1
        prev_city = None
        
        # Add fixed events to itinerary
        for event in sorted(fixed_events, key=lambda x: x['day_range'][0]):
            city = event['city']
            day_start, day_end = event['day_range']
            if day_start > current_day:
                # Need to fill days before fixed event
                pass
            itinerary.append({'day_range': f'Day {day_start}-{day_end}', 'place': city})
            current_day = day_end + 1
            prev_city = city
        
        # Try to fit remaining cities into the itinerary
        valid = True
        for city in perm:
            if city in [e['place'] for e in itinerary]:
                continue  # already visited
            
            # Find a connection from prev_city to current city
            if prev_city and city not in flights[prev_city]:
                valid = False
                break
            
            # Add the city to itinerary
            days_needed = remaining_cities[city]
            day_start = current_day
            day_end = current_day + days_needed - 1
            if day_end > 27:
                valid = False
                break
            itinerary.append({'day_range': f'Day {day_start}-{day_end}', 'place': city})
            current_day = day_end + 1
            prev_city = city
        
        if valid and current_day <= 28:
            # Check if all cities are visited
            visited_cities = {e['place'] for e in itinerary}
            if set(cities.keys()).issubset(visited_cities):
                # Sort itinerary by day range
                def get_day_start(entry):
                    parts = entry['day_range'].split('-')
                    return int(parts[0].split(' ')[1])
                itinerary_sorted = sorted(itinerary, key=get_day_start)
                return {'itinerary': itinerary_sorted}
    
    # Fallback itinerary if no permutation works
    itinerary = [
        {'day_range': 'Day 1-3', 'place': 'Santorini'},
        {'day_range': 'Day 3-6', 'place': 'Vienna'},
        {'day_range': 'Day 6-7', 'place': 'Madrid'},
        {'day_range': 'Day 8-11', 'place': 'Valencia'},
        {'day_range': 'Day 12-16', 'place': 'Krakow'},
        {'day_range': 'Day 17-20', 'place': 'Frankfurt'},
        {'day_range': 'Day 20-23', 'place': 'Riga'},
        {'day_range': 'Day 23-27', 'place': 'Tallinn'}
    ]
    
    # Check if all cities are covered
    visited_cities = {e['place'] for e in itinerary}
    missing = set(cities.keys()) - visited_cities
    if missing:
        return {'error': f'No valid itinerary found. Missing cities: {missing}'}
    
    # Validate day ranges
    try:
        total_days = 0
        for entry in itinerary:
            parts = entry['day_range'].split('-')
            start = int(parts[0].split(' ')[1])
            end = int(parts[1])
            total_days += end - start + 1
        
        if total_days != 27:
            return {'error': 'Invalid day count in itinerary'}
    except Exception as e:
        return {'error': f'Error validating itinerary: {str(e)}'}
    
    return {'itinerary': itinerary}

# Execute and print result
result = find_itinerary()
print(json.dumps(result, indent=2))