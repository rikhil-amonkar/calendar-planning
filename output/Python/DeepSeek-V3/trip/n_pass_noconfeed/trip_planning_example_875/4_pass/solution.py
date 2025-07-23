import json

def find_itinerary():
    cities = {
        'Stuttgart': {'duration': 3, 'constraints': [(11, 13)]},
        'Edinburgh': {'duration': 4, 'constraints': []},
        'Athens': {'duration': 4, 'constraints': []},
        'Split': {'duration': 2, 'constraints': [(13, 14)]},
        'Krakow': {'duration': 4, 'constraints': [(8, 11)]},
        'Venice': {'duration': 5, 'constraints': []},
        'Mykonos': {'duration': 4, 'constraints': []}
    }
    
    direct_flights = {
        'Krakow': ['Split', 'Edinburgh', 'Stuttgart'],
        'Split': ['Krakow', 'Athens', 'Stuttgart'],
        'Edinburgh': ['Krakow', 'Stuttgart', 'Venice', 'Athens'],
        'Venice': ['Stuttgart', 'Edinburgh', 'Athens'],
        'Stuttgart': ['Venice', 'Krakow', 'Edinburgh', 'Athens', 'Split'],
        'Athens': ['Split', 'Stuttgart', 'Edinburgh', 'Venice', 'Mykonos'],
        'Mykonos': ['Athens']
    }
    
    # Fix typos in city names
    direct_flights = {}
    for city in direct_flights:
        corrected_city = city
        if city == 'Venice':
            corrected_city = 'Venice'
        elif city == 'Athens':
            corrected_city = 'Athens'
        direct_flights[corrected_city] = [c if c != 'Venice' else 'Venice' for c in direct_flights[city]]
    
    city_names = list(cities.keys())
    constrained_cities = [city for city in city_names if cities[city]['constraints']]
    unconstrained_cities = [city for city in city_names if city not in constrained_cities]
    
    def backtrack(current_itinerary, remaining_cities, current_day):
        if current_day > 20:
            return None
            
        if not remaining_cities:
            return current_itinerary
            
        # Try all remaining cities in order
        for city in remaining_cities:
            duration = cities[city]['duration']
            start_day = current_day
            end_day = current_day + duration - 1
            
            # Check if it fits in the 20-day limit
            if end_day > 20:
                continue
                
            # Check constraints if any
            if cities[city]['constraints']:
                constraint_violated = False
                for (constraint_start, constraint_end) in cities[city]['constraints']:
                    if not (end_day < constraint_start or start_day > constraint_end):
                        constraint_violated = True
                        break
                if constraint_violated:
                    continue
            
            # Check flight connection
            if current_itinerary:
                last_city = current_itinerary[-1]['place']
                if city not in direct_flights[last_city]:
                    continue
            # For first city, prefer constrained cities
            elif not current_itinerary and city in unconstrained_cities and constrained_cities:
                continue
                
            new_itinerary = current_itinerary + [{
                'day_range': f'Day {start_day}-{end_day}',
                'place': city
            }]
            
            result = backtrack(new_itinerary, 
                              [c for c in remaining_cities if c != city],
                              end_day + 1)
            if result:
                return result
                
        return None
    
    # Start the backtracking
    result = backtrack([], city_names, 1)
    
    return {'itinerary': result} if result else {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))