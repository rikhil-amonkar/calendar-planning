import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Santorini': {'days': 5, 'constraints': [(25, 29)]},
        'Krakow': {'days': 5, 'constraints': [(18, 22)]},
        'Paris': {'days': 5, 'constraints': [(11, 15)]},
        'Vilnius': {'days': 3, 'constraints': []},
        'Munich': {'days': 5, 'constraints': []},
        'Geneva': {'days': 2, 'constraints': []},
        'Amsterdam': {'days': 4, 'constraints': []},
        'Budapest': {'days': 5, 'constraints': []},
        'Split': {'days': 4, 'constraints': []}
    }
    
    direct_flights = {
        'Paris': ['Krakow', 'Amsterdam', 'Split', 'Geneva', 'Budapest', 'Vilnius', 'Munich'],
        'Krakow': ['Paris', 'Split', 'Munich', 'Amsterdam', 'Vilnius'],
        'Vilnius': ['Munich', 'Split', 'Amsterdam', 'Paris', 'Krakow'],
        'Munich': ['Vilnius', 'Split', 'Amsterdam', 'Geneva', 'Krakow', 'Paris', 'Budapest'],
        'Geneva': ['Paris', 'Amsterdam', 'Split', 'Munich', 'Budapest', 'Santorini'],
        'Amsterdam': ['Paris', 'Geneva', 'Munich', 'Budapest', 'Split', 'Vilnius', 'Krakow', 'Santorini'],
        'Budapest': ['Amsterdam', 'Paris', 'Geneva', 'Munich'],
        'Split': ['Paris', 'Munich', 'Geneva', 'Amsterdam', 'Krakow', 'Vilnius'],
        'Santorini': ['Geneva', 'Amsterdam']
    }
    
    # Try different city orders
    constrained_cities = ['Paris', 'Krakow', 'Santorini']
    other_cities = [c for c in cities if c not in constrained_cities]
    
    # Try different starting points
    for start_city in ['Paris', 'Geneva', 'Amsterdam']:
        # Try different permutations of other cities
        for perm in permutations(other_cities):
            # Create a complete city order to try
            city_order = [start_city]
            # Insert constrained cities at appropriate positions
            for city in constrained_cities:
                # Find earliest position where it can be inserted with flight connection
                for i in range(len(city_order) + 1):
                    if i == 0:
                        prev_city = None
                    else:
                        prev_city = city_order[i-1]
                    
                    if i == len(city_order):
                        next_city = None
                    else:
                        next_city = city_order[i]
                    
                    # Check flight connections
                    valid = True
                    if prev_city and city not in direct_flights[prev_city]:
                        valid = False
                    if next_city and next_city not in direct_flights[city]:
                        valid = False
                    
                    if valid:
                        city_order.insert(i, city)
                        break
                else:
                    break  # couldn't place this constrained city
            
            if len(city_order) != len(constrained_cities) + 1:
                continue  # skip if couldn't place all constrained cities
            
            # Add the remaining cities
            for city in perm:
                if city not in city_order:
                    # Find a position to insert with valid flights
                    for i in range(len(city_order) + 1):
                        if i == 0:
                            prev_city = None
                        else:
                            prev_city = city_order[i-1]
                        
                        if i == len(city_order):
                            next_city = None
                        else:
                            next_city = city_order[i]
                        
                        valid = True
                        if prev_city and city not in direct_flights[prev_city]:
                            valid = False
                        if next_city and next_city not in direct_flights[city]:
                            valid = False
                        
                        if valid:
                            city_order.insert(i, city)
                            break
                    else:
                        break  # couldn't place this city
            
            if len(city_order) != len(cities):
                continue  # skip if couldn't place all cities
            
            # Now try to schedule the cities in this order
            itinerary = []
            current_day = 1
            valid_schedule = True
            
            for city in city_order:
                days_needed = cities[city]['days']
                constraints = cities[city].get('constraints', [])
                
                if constraints:
                    # Must schedule within constraint window
                    (start_constraint, end_constraint) = constraints[0]
                    start_day = max(current_day, start_constraint)
                    end_day = start_day + days_needed - 1
                    
                    if end_day > end_constraint or end_day > 30:
                        valid_schedule = False
                        break
                else:
                    # Can schedule anywhere with enough days
                    start_day = current_day
                    end_day = start_day + days_needed - 1
                    
                    if end_day > 30:
                        valid_schedule = False
                        break
                
                itinerary.append({
                    'day_range': f"Day {start_day}-{end_day}",
                    'place': city
                })
                current_day = end_day + 1
            
            if valid_schedule and len(itinerary) == len(cities):
                return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))