import json
from itertools import permutations

def generate_itinerary():
    # Input parameters
    total_days = 12
    city_stays = {
        'Hamburg': 2,
        'Zurich': 3,
        'Helsinki': 2,
        'Bucharest': 2,
        'Split': 7
    }
    wedding_in_zurich = (1, 3)  # between day 1 and day 3
    conference_in_split = (4, 10)  # between day 4 and day 10
    
    # Direct flights
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Hamburg': ['Zurich', 'Helsinki', 'Bucharest', 'Split'],
        'Bucharest': ['Zurich', 'Hamburg'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    cities = list(city_stays.keys())
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        itinerary = []
        current_day = 1
        prev_city = None
        
        for city in perm:
            if prev_city is not None:
                # Check if there's a direct flight
                if city not in direct_flights[prev_city]:
                    break
                # Add flying day
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 0  # Assuming flight doesn't take a full day
            
            stay_duration = city_stays[city]
            
            # Check constraints
            if city == 'Zurich':
                # Wedding must be between day 1 and 3
                if not (current_day <= wedding_in_zurich[0] and current_day + stay_duration - 1 >= wedding_in_zurich[1]):
                    break
            if city == 'Split':
                # Conference must be between day 4 and 10
                if not (current_day <= conference_in_split[1] and current_day + stay_duration - 1 >= conference_in_split[0]):
                    break
            
            itinerary.append({
                'day_range': f'Day {current_day}-{current_day + stay_duration - 1}',
                'place': city
            })
            current_day += stay_duration
            prev_city = city
        
        # Check if all cities are visited and total days is 12
        if current_day - 1 == total_days and len(itinerary) == 2 * len(cities) - 1:
            return itinerary
    
    return None

itinerary = generate_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))