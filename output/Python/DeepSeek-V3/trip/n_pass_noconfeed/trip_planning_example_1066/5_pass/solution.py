import json

def find_itinerary():
    # Cities and required days
    cities = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    # Special constraints
    conference_days = (20, 21)  # Madrid must be on these days
    stuttgart_friend_days = (1, 4)  # Stuttgart must include these days
    
    # Direct flights (bidirectional)
    flights = {
        'Helsinki': ['London', 'Madrid', 'Brussels', 'Split'],
        'Split': ['Madrid', 'Helsinki', 'London', 'Stuttgart'],
        'Madrid': ['Split', 'Helsinki', 'London', 'Mykonos', 'Bucharest', 'Brussels'],
        'London': ['Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Split', 'Mykonos', 'Stuttgart'],
        'Brussels': ['London', 'Bucharest', 'Helsinki', 'Madrid'],
        'Bucharest': ['London', 'Brussels', 'Madrid'],
        'Mykonos': ['Madrid', 'London'],
        'Stuttgart': ['London', 'Split']
    }
    
    # Fix typo in Brussels spelling in Helsinki's connections
    flights['Helsinki'] = ['London', 'Madrid', 'Brussels', 'Split']
    
    # We'll use backtracking to find a valid itinerary
    def backtrack(current_itinerary, remaining_cities, current_day, last_city):
        # Base case: all cities visited and Madrid is on days 20-21
        if not remaining_cities:
            if current_day == 20 and last_city in flights.get('Madrid', []):
                current_itinerary.append({'day_range': "Day 20-21", 'place': 'Madrid'})
                return current_itinerary.copy()
            return None
        
        # Try each remaining city that's connected to the last city
        for city in list(remaining_cities):
            # Check if we can fly to this city from the last city
            if last_city is None or city in flights.get(last_city, []):
                days_needed = cities[city]
                # Special case for Stuttgart (must be days 1-4)
                if city == 'Stuttgart':
                    if current_day != 1:
                        continue  # Stuttgart must start on day 1
                    days_needed = 4
                    new_day = current_day + days_needed
                    new_itinerary = current_itinerary.copy()
                    new_itinerary.append({'day_range': "Day 1-4", 'place': 'Stuttgart'})
                    result = backtrack(new_itinerary, remaining_cities - {city}, new_day, 'Stuttgart')
                    if result:
                        return result
                    continue
                
                # Special case for Madrid (must be last, days 20-21)
                if city == 'Madrid':
                    continue  # We'll handle Madrid separately at the end
                
                # Check if this city fits before day 20
                end_day = current_day + days_needed - 1
                if end_day >= 20:
                    continue  # Would overlap with Madrid
                
                # Try adding this city
                new_day = current_day + days_needed
                new_itinerary = current_itinerary.copy()
                new_itinerary.append({'day_range': f"Day {current_day}-{end_day}", 'place': city})
                result = backtrack(new_itinerary, remaining_cities - {city}, new_day, city)
                if result:
                    return result
        
        return None
    
    # Start the backtracking
    initial_cities = set(cities.keys()) - {'Madrid'}
    result = backtrack([], initial_cities, 1, None)
    
    if result:
        return {'itinerary': result}
    else:
        return {'itinerary': []}

# Execute and print result
result = find_itinerary()
print(json.dumps(result, indent=2))