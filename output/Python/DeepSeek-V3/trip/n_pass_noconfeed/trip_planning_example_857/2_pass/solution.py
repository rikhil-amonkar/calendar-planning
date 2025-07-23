import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Porto': {'days': 2, 'constraints': []},
        'Geneva': {'days': 3, 'constraints': []},
        'Mykonos': {'days': 3, 'constraints': [{'start': 10, 'end': 12}]},
        'Manchester': {'days': 4, 'constraints': [{'start': 15, 'end': 18}]},
        'Hamburg': {'days': 5, 'constraints': []},
        'Naples': {'days': 5, 'constraints': []},
        'Frankfurt': {'days': 2, 'constraints': [{'start': 5, 'end': 6}]}
    }
    
    flight_routes = {
        'Hamburg': ['Frankfurt', 'Porto', 'Geneva', 'Manchester'],
        'Frankfurt': ['Hamburg', 'Geneva', 'Porto', 'Naples', 'Manchester'],
        'Porto': ['Hamburg', 'Frankfurt', 'Geneva', 'Manchester'],
        'Geneva': ['Hamburg', 'Frankfurt', 'Porto', 'Mykonos', 'Manchester', 'Naples'],
        'Mykonos': ['Geneva', 'Naples'],
        'Naples': ['Mykonos', 'Frankfurt', 'Geneva', 'Manchester'],
        'Manchester': ['Geneva', 'Naples', 'Frankfurt', 'Porto', 'Hamburg']
    }
    
    # Prioritize cities with constraints
    constrained_cities = [city for city in cities if cities[city]['constraints']]
    other_cities = [city for city in cities if not cities[city]['constraints']]
    
    # Try different orders of constrained cities first
    for constrained_order in permutations(constrained_cities):
        # Try inserting other cities in different positions
        for other_order in permutations(other_cities):
            # Combine the orders
            city_order = list(constrained_order) + list(other_order)
            
            itinerary = []
            current_day = 1
            valid = True
            
            for i in range(len(city_order)):
                city = city_order[i]
                days_needed = cities[city]['days']
                
                # Check flight connection
                if i > 0:
                    prev_city = city_order[i-1]
                    if city not in flight_routes[prev_city]:
                        valid = False
                        break
                
                # Check constraints
                for constraint in cities[city]['constraints']:
                    start = constraint['start']
                    end = constraint['end']
                    # Check if the stay covers the required period
                    if not (current_day <= start and (current_day + days_needed - 1) >= end):
                        valid = False
                        break
                if not valid:
                    break
                
                # Check if we exceed 18 days
                if current_day + days_needed - 1 > 18:
                    valid = False
                    break
                
                day_range = f"Day {current_day}-{current_day + days_needed - 1}"
                itinerary.append({'day_range': day_range, 'place': city})
                current_day += days_needed
            
            if valid:
                return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result))