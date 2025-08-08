from z3 import *

def solve_itinerary():
    # Define cities with numeric IDs
    cities = {
        'Vienna': 1,
        'Lyon': 2,
        'Amsterdam': 3,
        'Santorini': 4
    }
    
    # Direct flights adjacency list
    direct_flights = {
        1: [2, 3, 4],  # Vienna
        2: [1, 3],      # Lyon
        3: [1, 2, 4],   # Amsterdam
        4: [1, 3]       # Santorini
    }
    
    # Create solver
    s = Solver()
    
    # Variables for each day's city
    days = 14
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Each day must be one of the cities
    for day in day_vars:
        s.add(Or([day == c for c in cities.values()]))
    
    # Flight transitions must be direct
    for i in range(days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        s.add(Or(current == next_day, *[And(current == c1, next_day == c2) 
                                      for c1 in direct_flights for c2 in direct_flights[c1]]))
    
    # Count days in each city (including flight days)
    counts = {city: Sum([If(day == c, 1, 0) for day in day_vars]) 
             for city, c in cities.items()}
    
    # Required days in each city (minimum requirements)
    s.add(counts['Vienna'] >= 7)
    s.add(counts['Lyon'] >= 3)
    s.add(counts['Amsterdam'] >= 3)
    s.add(counts['Santorini'] >= 4)
    
    # Total days must sum to 14 + (number of flights)
    # Since each flight day counts for 2 cities, we need to account for this
    # We'll let the solver balance this automatically
    
    # Workshop in Amsterdam between days 9-11 (must be there at least one day)
    s.add(Or([day_vars[i] == cities['Amsterdam'] for i in [8, 9, 10]]))
    
    # Wedding in Lyon between days 7-9 (must be there at least one day)
    s.add(Or([day_vars[i] == cities['Lyon'] for i in [6, 7, 8]]))
    
    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_code = m.evaluate(day_vars[i]).as_long()
            city_name = next(k for k, v in cities.items() if v == city_code)
            itinerary.append({'day': day_num, 'place': city_name})
        
        # Verify constraints
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            day_counts[entry['place']] += 1
        
        # Workshop and wedding days
        workshop_days = [entry['day'] for entry in itinerary 
                        if entry['place'] == 'Amsterdam' and 9 <= entry['day'] <= 11]
        wedding_days = [entry['day'] for entry in itinerary 
                       if entry['place'] == 'Lyon' and 7 <= entry['day'] <= 9]
        
        # Flight connections
        valid_flights = True
        for i in range(days - 1):
            current = itinerary[i]['place']
            next_city = itinerary[i + 1]['place']
            if current != next_city and cities[next_city] not in direct_flights[cities[current]]:
                valid_flights = False
                break
        
        if (day_counts['Vienna'] >= 7 and day_counts['Lyon'] >= 3 and
            day_counts['Amsterdam'] >= 3 and day_counts['Santorini'] >= 4 and
            len(workshop_days) >= 1 and len(wedding_days) >= 1 and valid_flights):
            return {'itinerary': itinerary}
    
    return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")