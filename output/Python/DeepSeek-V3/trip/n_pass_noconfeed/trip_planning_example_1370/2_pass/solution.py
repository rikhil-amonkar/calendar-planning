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
    
    # Prioritize cities with constraints first
    constrained_cities = [city for city in cities if cities[city]['constraints']]
    unconstrained_cities = [city for city in cities if not cities[city]['constraints']]
    
    # Try different orders of constrained cities first
    for constrained_order in permutations(constrained_cities):
        # Try different orders of unconstrained cities
        for unconstrained_order in permutations(unconstrained_cities):
            # Combine the orders
            city_order = list(constrained_order) + list(unconstrained_order)
            
            itinerary = []
            current_day = 1
            valid = True
            
            for i, city in enumerate(city_order):
                days_needed = cities[city]['days']
                constraints = cities[city]['constraints']
                
                # Check flight connections
                if i > 0:
                    prev_city = city_order[i-1]
                    if city not in direct_flights[prev_city]:
                        valid = False
                        break
                
                # Calculate potential stay
                start_day = current_day
                end_day = current_day + days_needed - 1
                
                # Check if this exceeds 30 days
                if end_day > 30:
                    valid = False
                    break
                
                # Check constraints
                for (constraint_start, constraint_end) in constraints:
                    if not (start_day <= constraint_end and end_day >= constraint_start):
                        valid = False
                        break
                
                if not valid:
                    break
                
                itinerary.append({
                    'day_range': f"Day {start_day}-{end_day}",
                    'place': city
                })
                current_day = end_day + 1
            
            if valid:
                return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))