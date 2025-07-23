import json

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
    
    # Fix any typos in city names
    flight_routes['Reykjavik'] = ['Helsinki', 'Warsaw', 'Budapest', 'Madrid']
    
    def backtrack(current_itinerary, remaining_cities, current_day, last_city):
        if current_day > 14:
            # Check if all constraints are satisfied
            day_assignments = {}
            day = 1
            for item in current_itinerary:
                city = item['place']
                days = cities[city]['days']
                for d in range(day, day + days):
                    day_assignments[d] = city
                day += days
            
            # Check all constraints
            for city in cities:
                for (start, end) in cities[city]['constraints']:
                    satisfied = False
                    for day in range(start, end + 1):
                        if day_assignments.get(day) == city:
                            satisfied = True
                            break
                    if not satisfied:
                        return None
            
            return current_itinerary
        
        if not remaining_cities:
            return None
        
        for city in remaining_cities:
            if last_city is None or city in flight_routes[last_city]:
                days_needed = cities[city]['days']
                if current_day + days_needed - 1 > 14:
                    continue
                
                new_itinerary = current_itinerary.copy()
                new_itinerary.append({
                    'day_range': f"Day {current_day}-{current_day + days_needed - 1}",
                    'place': city
                })
                
                new_remaining = remaining_cities.copy()
                new_remaining.remove(city)
                
                result = backtrack(
                    new_itinerary,
                    new_remaining,
                    current_day + days_needed,
                    city
                )
                
                if result is not None:
                    return result
        
        return None
    
    # Start with all cities remaining
    remaining_cities = set(cities.keys())
    
    # First handle cities with constraints
    constrained_cities = [city for city in cities if cities[city]['constraints']]
    
    for city in constrained_cities:
        for (start, end) in cities[city]['constraints']:
            # Try to place this city within its constraint period
            for start_day in range(start, end - cities[city]['days'] + 2):
                end_day = start_day + cities[city]['days'] - 1
                if end_day > end:
                    continue
                
                # Create initial itinerary with this placement
                initial_itinerary = [{
                    'day_range': f"Day {start_day}-{end_day}",
                    'place': city
                }]
                
                remaining = remaining_cities - {city}
                
                # Try to build the rest of the itinerary
                result = backtrack(
                    initial_itinerary,
                    remaining,
                    end_day + 1,
                    city
                )
                
                if result is not None:
                    return {"itinerary": result}
    
    # If no solution found with constrained cities first, try without
    result = backtrack([], list(remaining_cities), 1, None)
    if result is not None:
        return {"itinerary": result}
    
    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))