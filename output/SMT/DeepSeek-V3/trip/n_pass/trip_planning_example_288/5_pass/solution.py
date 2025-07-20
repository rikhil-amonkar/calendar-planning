from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    man, stut, mad, vie = cities
    
    # Create Z3 variables for each day (1-15)
    s = Solver()
    day_to_city = [Int(f'day_{i}') for i in range(1, 16)]
    
    # City mapping
    city_map = {man: 0, stut: 1, mad: 2, vie: 3}
    inv_city_map = {v: k for k, v in city_map.items()}
    
    # Ensure each day is assigned a valid city
    for day in day_to_city:
        s.add(day >= 0, day <= 3)
    
    # Manchester must be days 1-7 (wedding)
    for day in range(7):
        s.add(day_to_city[day] == city_map[man])
    
    # Stuttgart must have at least one day between 11-15 (workshop)
    s.add(Or([day_to_city[i] == city_map[stut] for i in range(10, 15)]))
    
    # Transition constraints (direct flights)
    direct_connections = [
        (city_map[man], city_map[stut]),
        (city_map[man], city_map[mad]),
        (city_map[man], city_map[vie]),
        (city_map[stut], city_map[man]),
        (city_map[stut], city_map[vie]),
        (city_map[mad], city_map[man]),
        (city_map[mad], city_map[vie]),
        (city_map[vie], city_map[man]),
        (city_map[vie], city_map[stut]),
        (city_map[vie], city_map[mad])
    ]
    
    for i in range(14):
        current = day_to_city[i]
        next_day = day_to_city[i+1]
        s.add(Or(current == next_day, *[And(current == a, next_day == b) for (a,b) in direct_connections]))
    
    # Count days in each city
    man_days = Sum([If(day_to_city[i] == city_map[man], 1, 0) for i in range(15)])
    stut_days = Sum([If(day_to_city[i] == city_map[stut], 1, 0) for i in range(15)])
    mad_days = Sum([If(day_to_city[i] == city_map[mad], 1, 0) for i in range(15)])
    vie_days = Sum([If(day_to_city[i] == city_map[vie], 1, 0) for i in range(15)])
    
    s.add(man_days == 7)
    s.add(stut_days == 5)
    s.add(mad_days == 4)
    s.add(vie_days == 2)
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 16):
            city_num = model.evaluate(day_to_city[day-1]).as_long()
            itinerary.append({'day': day, 'place': inv_city_map[city_num]})
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")