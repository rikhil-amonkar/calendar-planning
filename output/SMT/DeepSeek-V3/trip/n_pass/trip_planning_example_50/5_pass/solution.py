from z3 import *

def solve_itinerary():
    s = Solver()
    
    # Days are 1 to 12 inclusive
    days = 12
    cities = ['Vilnius', 'Munich', 'Mykonos']
    city_code = {c:i for i,c in enumerate(cities)}
    
    # Decision variables for each day's city
    day_city = [Int(f'day_{i}') for i in range(1, days+1)]
    
    # Each day must be one of the three cities
    for dc in day_city:
        s.add(And(dc >= 0, dc <= 2))
    
    # Flight transition constraints
    for i in range(days-1):
        current = day_city[i]
        next_day = day_city[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current == 0, next_day == 1),  # Vilnius -> Munich
            And(current == 1, next_day == 0),  # Munich -> Vilnius
            And(current == 1, next_day == 2),  # Munich -> Mykonos
            And(current == 2, next_day == 1)   # Mykonos -> Munich
        ))
    
    # Count days in each city
    vilnius_days = Sum([If(dc == 0, 1, 0) for dc in day_city])
    munich_days = Sum([If(dc == 1, 1, 0) for dc in day_city])
    mykonos_days = Sum([If(dc == 2, 1, 0) for dc in day_city])
    
    s.add(vilnius_days == 4)
    s.add(munich_days == 3)
    s.add(mykonos_days == 7)
    
    # Start in Vilnius or Munich (Mykonos not directly reachable from Vilnius)
    s.add(Or(day_city[0] == 0, day_city[0] == 1))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, days+1):
            city_idx = m.evaluate(day_city[day-1]).as_long()
            itinerary.append({"day": day, "place": cities[city_idx]})
        
        # Verify day counts
        counts = {c:0 for c in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        assert counts['Vilnius'] == 4
        assert counts['Munich'] == 3
        assert counts['Mykonos'] == 7
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))