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
    
    # Correcting some typos in the flight routes
    flight_routes['Helsinki'] = ['Reykjavik', 'Split', 'Madrid', 'Budapest', 'Warsaw']
    flight_routes['Madrid'] = ['Split', 'Helsinki', 'Budapest', 'Warsaw']
    flight_routes['Split'] = ['Madrid', 'Helsinki', 'Warsaw']
    flight_routes['Budapest'] = ['Warsaw', 'Helsinki', 'Madrid', 'Reykjavik']
    
    city_names = list(cities.keys())
    
    def is_valid_route(route):
        for i in range(len(route) - 1):
            if route[i+1] not in flight_routes[route[i]]:
                return False
        return True
    
    def satisfies_constraints(assignment):
        day_place = {}
        for day in range(1, 15):
            day_place[day] = None
        
        current_day = 1
        for city in assignment:
            days_spent = cities[city]['days']
            end_day = current_day + days_spent - 1
            if end_day > 14:
                return False
            
            for day in range(current_day, end_day + 1):
                day_place[day] = city
            current_day = end_day + 1
        
        # Check constraints
        for city in cities:
            constraints = cities[city]['constraints']
            for (start, end) in constraints:
                found = False
                for day in range(start, end + 1):
                    if day_place.get(day) == city:
                        found = True
                        break
                if not found:
                    return False
        
        return True
    
    # Generate all permutations of cities and check for valid routes
    for perm in permutations(city_names):
        if is_valid_route(perm) and satisfies_constraints(perm):
            itinerary = []
            current_day = 1
            for city in perm:
                days_spent = cities[city]['days']
                end_day = current_day + days_spent - 1
                if end_day > 14:
                    break
                day_range = f"Day {current_day}-{end_day}"
                itinerary.append({"day_range": day_range, "place": city})
                current_day = end_day + 1
            
            if current_day > 14:
                return {"itinerary": itinerary}
    
    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result))