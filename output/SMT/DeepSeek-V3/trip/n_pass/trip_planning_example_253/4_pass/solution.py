from z3 import *

def solve_itinerary():
    # Cities: Amsterdam (A), Vienna (V), Santorini (S), Lyon (L)
    cities = ['A', 'V', 'S', 'L']
    city_map = {'A': 'Amsterdam', 'V': 'Vienna', 'S': 'Santorini', 'L': 'Lyon'}
    n_days = 14
    
    # Direct flights: adjacency list
    direct_flights = {
        'V': ['L', 'S', 'A'],
        'A': ['V', 'S', 'L'],
        'S': ['V', 'A'],
        'L': ['V', 'A']
    }
    
    # Create Z3 variables for each day: 1..14
    day_vars = [Int(f"day_{i}") for i in range(1, n_days + 1)]
    
    s = Solver()
    
    # Each day variable must be 0 (A), 1 (V), 2 (S), or 3 (L)
    for day in day_vars:
        s.add(Or([day == 0, day == 1, day == 2, day == 3]))
    
    # Total days per city constraints
    # A: 3 days, V: 7, S:4, L:3
    total_A = Sum([If(day == 0, 1, 0) for day in day_vars])
    total_V = Sum([If(day == 1, 1, 0) for day in day_vars])
    total_S = Sum([If(day == 2, 1, 0) for day in day_vars])
    total_L = Sum([If(day == 3, 1, 0) for day in day_vars])
    
    s.add(total_A == 3)
    s.add(total_V == 7)
    s.add(total_S == 4)
    s.add(total_L == 3)
    
    # Workshop in Amsterdam between day 9 and 11 (inclusive)
    workshop_days = [If(day_vars[i] == 0, 1, 0) for i in range(8, 11)]  # days 9-11 (1-based)
    s.add(Sum(workshop_days) >= 1)
    
    # Wedding in Lyon between day 7 and 9 (inclusive)
    wedding_days = [If(day_vars[i] == 3, 1, 0) for i in range(6, 9)]  # days 7-9 (1-based)
    s.add(Sum(wedding_days) >= 1)
    
    # Flight constraints: consecutive days must be either same city or connected by direct flight
    for i in range(n_days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        # Either same city or flight exists
        same_city = (current_city == next_city)
        flight_possible = Or([And(current_city == ci, next_city == cj) 
                            for ci, city in enumerate(cities) 
                            for cj, target in enumerate(cities) 
                            if city != target and target in direct_flights[city]])
        s.add(Or(same_city, flight_possible))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            city_code = cities[m.evaluate(day_vars[i]).as_long()]
            itinerary.append({"day": i + 1, "place": city_map[city_code]})
        
        # Verify the counts
        counts = {'A': 0, 'V': 0, 'S': 0, 'L': 0}
        for entry in itinerary:
            place = entry['place'][0]  # first letter
            counts[place] += 1
        assert counts['A'] == 3 and counts['V'] ==7 and counts['S'] ==4 and counts['L'] ==3, "Counts do not match"
        
        # Verify workshop and wedding days
        workshop_ok = any(9 <= entry['day'] <=11 and entry['place'] == 'Amsterdam' for entry in itinerary)
        wedding_ok = any(7 <= entry['day'] <=9 and entry['place'] == 'Lyon' for entry in itinerary)
        assert workshop_ok and wedding_ok, "Event constraints not met"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))