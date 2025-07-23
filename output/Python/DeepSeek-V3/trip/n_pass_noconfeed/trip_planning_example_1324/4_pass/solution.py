import json
from collections import defaultdict

def find_itinerary():
    cities = {
        'Venice': 4,
        'Barcelona': 3,
        'Copenhagen': 4,
        'Lyon': 4,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 2,
        'Tallinn': 5,
        'Munich': 3
    }
    
    constraints = {
        'Barcelona': {'day_range': (10, 12)},
        'Copenhagen': {'day_range': (7, 10)},
        'Dubrovnik': {'day_range': (16, 20)}
    }
    
    direct_flights = {
        'Copenhagen': ['Athens', 'Dubrovnik', 'Munich', 'Reykjavik', 'Barcelona', 'Tallinn', 'Venice'],
        'Munich': ['Tallinn', 'Copenhagen', 'Venice', 'Reykjavik', 'Athens', 'Lyon', 'Dubrovnik', 'Barcelona'],
        'Venice': ['Munich', 'Athens', 'Copenhagen', 'Barcelona', 'Lyon'],
        'Reykjavik': ['Athens', 'Copenhagen', 'Munich', 'Barcelona'],
        'Athens': ['Copenhagen', 'Dubrovnik', 'Venice', 'Reykjavik', 'Munich', 'Barcelona'],
        'Lyon': ['Barcelona', 'Munich', 'Venice'],
        'Barcelona': ['Lyon', 'Dubrovnik', 'Athens', 'Reykjavik', 'Copenhagen', 'Venice', 'Munich', 'Tallinn'],
        'Dubrovnik': ['Copenhagen', 'Athens', 'Barcelona', 'Munich'],
        'Tallinn': ['Munich', 'Copenhagen', 'Barcelona']
    }
    
    def is_valid_move(last_city, next_city, current_day, duration):
        # Check flight connection
        if last_city and next_city not in direct_flights.get(last_city, []):
            return False
        
        # Check constraints
        if next_city in constraints:
            constr_start, constr_end = constraints[next_city]['day_range']
            visit_start = current_day
            visit_end = current_day + duration - 1
            # The visit must be completely within the constrained period
            if not (visit_start >= constr_start and visit_end <= constr_end):
                return False
        
        return True
    
    def backtrack(current_itinerary, remaining_cities, current_day, best_solution):
        if current_day > 26:
            return
        
        if not remaining_cities:
            if len(current_itinerary) == len(cities):
                best_solution.append(current_itinerary.copy())
            return
        
        last_city = current_itinerary[-1]['place'] if current_itinerary else None
        
        # Try cities with constraints first
        for city in sorted(remaining_cities, key=lambda x: x in constraints, reverse=True):
            duration = cities[city]
            
            if not is_valid_move(last_city, city, current_day, duration):
                continue
                
            day_range = (current_day, current_day + duration - 1)
            new_entry = {'day_range': f"Day {day_range[0]}-{day_range[1]}", 'place': city}
            current_itinerary.append(new_entry)
            
            backtrack(current_itinerary, remaining_cities - {city}, current_day + duration, best_solution)
                
            current_itinerary.pop()
    
    all_cities = set(cities.keys())
    best_solution = []
    
    # Try different starting cities
    for start_city in all_cities:
        # Skip if starting city has constraints that can't be met
        if start_city in constraints:
            constr_start, constr_end = constraints[start_city]['day_range']
            duration = cities[start_city]
            if not (1 >= constr_start and duration <= constr_end):
                continue
        
        duration = cities[start_city]
        day_range = (1, duration)
        itinerary = [{'day_range': f"Day {day_range[0]}-{day_range[1]}", 'place': start_city}]
        backtrack(itinerary, all_cities - {start_city}, duration + 1, best_solution)
        if best_solution:
            break  # Stop if we found a solution
    
    if best_solution:
        return {'itinerary': best_solution[0]}
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))