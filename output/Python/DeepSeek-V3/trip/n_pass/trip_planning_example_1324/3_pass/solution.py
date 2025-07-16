import json

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
        'Reykjavik': ['Athens', 'Munich', 'Barcelona', 'Copenhagen'],
        'Athens': ['Copenhagen', 'Dubrovnik', 'Venice', 'Reykjavik', 'Munich', 'Barcelona'],
        'Lyon': ['Barcelona', 'Munich', 'Venice'],
        'Barcelona': ['Lyon', 'Dubrovnik', 'Athens', 'Reykjavik', 'Copenhagen', 'Venice', 'Munich', 'Tallinn'],
        'Dubrovnik': ['Copenhagen', 'Athens', 'Barcelona', 'Munich'],
        'Tallinn': ['Munich', 'Barcelona', 'Copenhagen']
    }
    
    def backtrack(current_itinerary, remaining_cities, current_day, last_city=None):
        if current_day == 27 and not remaining_cities:
            return current_itinerary
        
        if current_day > 26:
            return None
        
        # Try all possible cities that can be visited next
        for city in list(remaining_cities):
            duration = cities[city]
            end_day = current_day + duration - 1
            
            # Check if this would exceed 26 days
            if end_day > 26:
                continue
                
            # Check city constraints
            if city in constraints:
                constr_start, constr_end = constraints[city]['day_range']
                if not (current_day <= constr_end and end_day >= constr_start):
                    continue
            
            # Check flight connection if not first city
            if last_city is not None:
                if city not in direct_flights.get(last_city, []):
                    continue
            
            # Try this city
            new_itinerary = current_itinerary.copy()
            new_itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            
            new_remaining = remaining_cities.copy()
            new_remaining.remove(city)
            
            result = backtrack(new_itinerary, new_remaining, end_day + 1, city)
            if result is not None:
                return result
        
        return None
    
    result = backtrack([], set(cities.keys()), 1)
    return {'itinerary': result} if result else {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))