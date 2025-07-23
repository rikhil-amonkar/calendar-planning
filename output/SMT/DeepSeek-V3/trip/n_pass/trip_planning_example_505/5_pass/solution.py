import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Prague': 4,
        'Stuttgart': 2,
        'Split': 2,
        'Krakow': 2,
        'Florence': 2
    }
    
    # Direct flights (bidirectional)
    direct_flights = {
        'Stuttgart': ['Split', 'Krakow'],
        'Split': ['Stuttgart', 'Krakow', 'Prague'],
        'Prague': ['Split', 'Florence'],
        'Krakow': ['Stuttgart', 'Split', 'Prague'],
        'Florence': ['Prague']
    }
    
    # Create solver
    s = Solver()
    
    # Variables: for each day (1-8), which city are we in
    # Each day can be in 1 city (stay) or 2 cities (travel day)
    days = 8
    itinerary = [[Int(f'day_{day}_city_{i}') for i in range(2)] for day in range(1, days+1)]
    
    # City encodings
    city_ids = {city: idx for idx, city in enumerate(cities)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraints for each day
    for day in range(days):
        day_vars = itinerary[day]
        
        # First city must be valid
        s.add(Or([day_vars[0] == city_ids[city] for city in cities]))
        
        # Second city is either -1 (no travel) or a valid city
        s.add(Or(day_vars[1] == -1, 
                And([day_vars[1] != day_vars[0],
                    Or([day_vars[1] == city_ids[city] for city in cities])])))
    
    # Flight connections between consecutive days
    for day in range(days-1):
        current = itinerary[day]
        next_day = itinerary[day+1]
        
        # Case 1: No travel on current day
        case1 = And(current[1] == -1,
                   Or([And(current[0] == city_ids[a], 
                          next_day[0] == city_ids[b])
                      for a in cities 
                      for b in direct_flights.get(a, [])]))
        
        # Case 2: Travel on current day
        case2 = And(current[1] != -1,
                   Or([And(current[1] == city_ids[a],
                           next_day[0] == city_ids[b])
                      for a in cities
                      for b in direct_flights.get(a, [])]))
        
        s.add(Or(case1, case2))
    
    # Count days in each city
    for city, required in cities.items():
        total = 0
        for day in range(days):
            day_vars = itinerary[day]
            total += If(Or(day_vars[0] == city_ids[city], 
                        day_vars[1] == city_ids[city]), 1, 0)
        s.add(total == required)
    
    # Event constraints
    # Wedding in Stuttgart between day 2-3 (days 1-2 in 0-based)
    s.add(Or(
        Or(itinerary[1][0] == city_ids['Stuttgart'], itinerary[1][1] == city_ids['Stuttgart']),
        Or(itinerary[2][0] == city_ids['Stuttgart'], itinerary[2][1] == city_ids['Stuttgart'])
    ))
    
    # Meeting in Split between day 3-4 (days 2-3 in 0-based)
    s.add(Or(
        Or(itinerary[2][0] == city_ids['Split'], itinerary[2][1] == city_ids['Split']),
        Or(itinerary[3][0] == city_ids['Split'], itinerary[3][1] == city_ids['Split'])
    ))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        result = {'itinerary': []}
        for day in range(days):
            day_vars = itinerary[day]
            cities_day = []
            
            # First city
            val1 = m[day_vars[0]].as_long()
            cities_day.append(id_to_city[val1])
            
            # Second city if exists
            val2 = m[day_vars[1]].as_long() if str(day_vars[1]) in [str(k) for k in m.decls()] else -1
            if val2 != -1:
                cities_day.append(id_to_city[val2])
            
            result['itinerary'].append({
                'day': day+1,
                'cities': cities_day
            })
        return result
    else:
        return {"error": "No valid itinerary found"}

solution = solve_itinerary()
print(json.dumps(solution, indent=2))