import json
from itertools import permutations

def find_itinerary():
    # Define the cities and their required days
    cities = {
        'Paris': 5,
        'Florence': 3,
        'Vienna': 2,
        'Porto': 3,
        'Munich': 5,
        'Nice': 5,
        'Warsaw': 3
    }
    
    # Define the direct flights
    direct_flights = {
        'Florence': ['Vienna', 'Munich', 'Paris'],
        'Vienna': ['Florence', 'Munich', 'Porto', 'Warsaw', 'Paris', 'Nice'],
        'Paris': ['Warsaw', 'Florence', 'Vienna', 'Porto', 'Nice', 'Munich'],
        'Munich': ['Vienna', 'Florence', 'Warsaw', 'Nice', 'Porto', 'Paris'],
        'Porto': ['Vienna', 'Munich', 'Nice', 'Paris', 'Warsaw'],
        'Nice': ['Munich', 'Warsaw', 'Vienna', 'Porto', 'Paris'],
        'Warsaw': ['Paris', 'Vienna', 'Munich', 'Nice', 'Porto']
    }
    
    # Fixed constraints
    fixed_constraints = [
        ('Porto', (1, 3)),
        ('Warsaw', (13, 15)),
        ('Vienna', (19, 20))
    ]
    
    # Other cities to place: Paris, Florence, Munich, Nice
    remaining_cities = ['Paris', 'Florence', 'Munich', 'Nice']
    
    # Generate possible permutations of the remaining cities
    for perm in permutations(remaining_cities):
        itinerary = []
        current_day = 1
        valid = True
        
        # Add Porto first (fixed)
        itinerary.append({'day_range': 'Day 1-3', 'place': 'Porto'})
        current_day = 4
        
        # Try to place the remaining cities between Porto and Warsaw
        temp_itinerary = itinerary.copy()
        temp_day = current_day
        remaining_cities_perm = list(perm)
        
        # Place remaining cities before Warsaw
        for city in remaining_cities_perm:
            duration = cities[city]
            end_day = temp_day + duration - 1
            
            # Must finish before Warsaw starts (day 13)
            if end_day >= 13:
                valid = False
                break
            
            temp_itinerary.append({'day_range': f'Day {temp_day}-{end_day}', 'place': city})
            temp_day = end_day + 1
        
        if not valid:
            continue
        
        # Add Warsaw (fixed)
        temp_itinerary.append({'day_range': 'Day 13-15', 'place': 'Warsaw'})
        
        # Now place any remaining time between Warsaw and Vienna
        current_day = 16
        
        # Check if we have any days left between Warsaw and Vienna
        if current_day < 19:
            # We have days 16-18 to potentially split among cities
            # But all cities are already placed in the permutation
            # So we might need to adjust our approach
            pass
        
        # Add Vienna (fixed)
        temp_itinerary.append({'day_range': 'Day 19-20', 'place': 'Vienna'})
        
        # Verify all cities are placed and days sum to 20
        total_days = 0
        placed_cities = set()
        for entry in temp_itinerary:
            day_range = entry['day_range']
            if '-' in day_range:
                start, end = map(int, day_range.split('-')[0].split(' ')[1:])
                total_days += (end - start + 1)
            placed_cities.add(entry['place'])
        
        if total_days != 20 or len(placed_cities) != 7:
            continue
        
        # Check flight connections
        prev_city = None
        flight_valid = True
        for i in range(len(temp_itinerary)):
            current_city = temp_itinerary[i]['place']
            if prev_city is not None and prev_city != current_city:
                if current_city not in direct_flights.get(prev_city, []):
                    flight_valid = False
                    break
            prev_city = current_city
        
        if flight_valid:
            return {'itinerary': temp_itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result))