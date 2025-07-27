from z3 import *

def solve_itinerary():
    # Cities and their IDs
    city_ids = {'Split': 0, 'Santorini': 1, 'London': 2}
    id_to_city = {0: 'Split', 1: 'Santorini', 2: 'London'}
    
    # Total days
    days = 18
    day_city = [Int(f'day_{i}') for i in range(1, days+1)]
    
    s = Solver()
    
    # Each day must be one of the three cities
    for day in day_city:
        s.add(Or([day == city_ids[city] for city in city_ids]))
    
    # Flight constraints - only direct flights allowed
    for i in range(days-1):
        current = day_city[i]
        next_day = day_city[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current == city_ids['Split'], next_day == city_ids['London']),
            And(current == city_ids['London'], next_day == city_ids['Split']),
            And(current == city_ids['London'], next_day == city_ids['Santorini']),
            And(current == city_ids['Santorini'], next_day == city_ids['London'])
        ))
    
    # Count days in each city (including flight days)
    split_days = Sum([If(day == city_ids['Split'], 1, 0) for day in day_city])
    santorini_days = Sum([If(day == city_ids['Santorini'], 1, 0) for day in day_city])
    london_days = Sum([If(day == city_ids['London'], 1, 0) for day in day_city])
    
    s.add(split_days == 6)
    s.add(santorini_days == 7)
    s.add(london_days == 7)
    
    # Must be in Santorini on days 12 and 18
    s.add(day_city[11] == city_ids['Santorini'])  # Day 12
    s.add(day_city[17] == city_ids['Santorini'])  # Day 18
    
    # Additional constraints to guide the solver
    # Start in Split (arbitrary choice to reduce search space)
    s.add(day_city[0] == city_ids['Split'])
    
    # Must have at least one transition between cities
    s.add(Or([day_city[i] != day_city[i+1] for i in range(days-1)]))
    
    # Ensure we don't have impossible sequences like Split->Santorini
    for i in range(days-1):
        s.add(Not(And(day_city[i] == city_ids['Split'], day_city[i+1] == city_ids['Santorini'])))
        s.add(Not(And(day_city[i] == city_ids['Santorini'], day_city[i+1] == city_ids['Split'])))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_id = m.evaluate(day_city[i]).as_long()
            itinerary.append({'day': i+1, 'place': id_to_city[city_id]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))