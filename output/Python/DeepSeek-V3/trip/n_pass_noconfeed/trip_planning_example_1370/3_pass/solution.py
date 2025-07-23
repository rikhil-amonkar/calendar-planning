import json

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
    
    # Start with constrained cities and schedule them first
    constrained_cities = ['Paris', 'Krakow', 'Santorini']
    
    # Try different starting points
    for start_city in ['Paris', 'Geneva', 'Amsterdam']:
        itinerary = []
        current_day = 1
        visited = set()
        
        # First schedule constrained cities
        for city in constrained_cities:
            if city in visited:
                continue
                
            days_needed = cities[city]['days']
            constraints = cities[city]['constraints'][0]
            
            # Try to schedule during the constrained period
            start_day = max(constraints[0], current_day)
            end_day = start_day + days_needed - 1
            
            if end_day > constraints[1] or end_day > 30:
                continue  # Skip if can't fit in constraints
            
            # Check if we can reach this city from previous
            if itinerary:
                prev_city = itinerary[-1]['place']
                if city not in direct_flights[prev_city]:
                    continue
            
            itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': city
            })
            visited.add(city)
            current_day = end_day + 1
        
        # Now schedule unconstrained cities
        unconstrained_cities = [c for c in cities if c not in constrained_cities]
        
        for city in unconstrained_cities:
            if city in visited:
                continue
                
            days_needed = cities[city]['days']
            start_day = current_day
            end_day = start_day + days_needed - 1
            
            if end_day > 30:
                continue
                
            if itinerary:
                prev_city = itinerary[-1]['place']
                if city not in direct_flights[prev_city]:
                    continue
            
            itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': city
            })
            visited.add(city)
            current_day = end_day + 1
        
        # Check if all cities are visited
        if len(visited) == len(cities):
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))