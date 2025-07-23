import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Helsinki': {'days': 2, 'constraints': [(1, 2)]},
        'Warsaw': {'days': 3, 'constraints': [(9, 11)]},
        'Madrid': {'days': 4, 'constraints': []},
        'Split': {'days': 4, 'constraints': []},
        'Reykjavik': {'days': 2, 'constraints': [(8, 9)]},
        'Budapest': {'days': 4, 'constraints': []}
    }
    
    flight_routes = {
        'Helsinki': ['Reykjavik', 'Split', 'Madrid', 'Budapest', 'Warsaw'],
        'Reykjavik': ['Helsinki', 'Warsaw', 'Budapest', 'Madrid'],
        'Budapest': ['Warsaw', 'Helsinki', 'Madrid', 'Reykjavik'],
        'Warsaw': ['Budapest', 'Reykjavik', 'Helsinki', 'Madrid', 'Split'],
        'Madrid': ['Split', 'Helsinki', 'Budapest', 'Warsaw'],
        'Split': ['Madrid', 'Helsinki', 'Warsaw']
    }
    
    def is_valid_itinerary(itinerary):
        # Check all days are covered without overlap
        days = [False] * 15  # Days 1-14 (index 1-14)
        day_assignments = {}
        
        current_day = 1
        for entry in itinerary:
            city = entry['place']
            duration = cities[city]['days']
            start_day = current_day
            end_day = current_day + duration - 1
            
            if end_day > 14:
                return False
            
            # Check for overlaps
            for day in range(start_day, end_day + 1):
                if days[day]:
                    return False
                days[day] = True
                day_assignments[day] = city
            
            current_day = end_day + 1
        
        # Check all cities are visited
        visited_cities = set(entry['place'] for entry in itinerary)
        if visited_cities != set(cities.keys()):
            return False
        
        # Check flight connections
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if next_city not in flight_routes[current_city]:
                return False
        
        # Check constraints
        for city in cities:
            for (start, end) in cities[city]['constraints']:
                satisfied = False
                for day in range(start, end + 1):
                    if day_assignments.get(day) == city:
                        satisfied = True
                        break
                if not satisfied:
                    return False
        
        return True
    
    # Generate all possible permutations of cities
    city_names = list(cities.keys())
    
    # Prioritize cities with constraints first
    constrained_cities = [city for city in cities if cities[city]['constraints']]
    other_cities = [city for city in cities if city not in constrained_cities]
    
    # Try different orders of constrained cities first
    for constrained_order in permutations(constrained_cities):
        for other_order in permutations(other_cities):
            # Combine the orders
            order = list(constrained_order) + list(other_order)
            
            # Try to build itinerary with this order
            current_day = 1
            itinerary = []
            valid = True
            
            for city in order:
                duration = cities[city]['days']
                end_day = current_day + duration - 1
                
                if end_day > 14:
                    valid = False
                    break
                
                itinerary.append({
                    'day_range': f"Day {current_day}-{end_day}",
                    'place': city
                })
                
                current_day = end_day + 1
            
            if valid and is_valid_itinerary(itinerary):
                return {"itinerary": itinerary}
    
    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))