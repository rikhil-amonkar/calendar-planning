from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    man, stut, mad, vie = cities
    
    # Direct flight connections
    direct_flights = {
        man: [stut, mad, vie],
        stut: [man, vie],
        mad: [man, vie],
        vie: [man, stut, mad]
    }
    
    # Create Z3 variables for each day (1-15)
    s = Solver()
    day_to_city = [Int(f'day_{i}') for i in range(1, 16)]  # 1-15
    
    # Assign each day's city to a number (0: Manchester, 1: Stuttgart, 2: Madrid, 3: Vienna)
    city_map = {man: 0, stut: 1, mad: 2, vie: 3}
    inv_city_map = {v: k for k, v in city_map.items()}
    
    for day in day_to_city:
        s.add(day >= 0, day <= 3)
    
    # Constraints for transitions: consecutive days must be same city or connected by direct flight
    for i in range(14):  # days 1-14, check transition to next day
        current_day = day_to_city[i]
        next_day = day_to_city[i+1]
        # Either same city or connected by direct flight
        s.add(Or(
            current_day == next_day,
            And(current_day == city_map[man], next_day == city_map[stut]),
            And(current_day == city_map[man], next_day == city_map[mad]),
            And(current_day == city_map[man], next_day == city_map[vie]),
            And(current_day == city_map[stut], next_day == city_map[man]),
            And(current_day == city_map[stut], next_day == city_map[vie]),
            And(current_day == city_map[mad], next_day == city_map[man]),
            And(current_day == city_map[mad], next_day == city_map[vie]),
            And(current_day == city_map[vie], next_day == city_map[man]),
            And(current_day == city_map[vie], next_day == city_map[stut]),
            And(current_day == city_map[vie], next_day == city_map[mad])
        ))
    
    # Manchester: 7 days, wedding between day 1-7 (so must be in Manchester days 1-7)
    for day in range(7):  # days 1-7 (0-based index 0-6)
        s.add(day_to_city[day] == city_map[man])
    
    # Stuttgart: 5 days, workshop between day 11-15 (must be in Stuttgart during some of these days)
    # Total Stuttgart days is 5, and at least one day between 11-15 is in Stuttgart.
    stuttgart_days = [If(day_to_city[i] == city_map[stut], 1, 0) for i in range(10, 15)]  # days 11-15 (indices 10-14)
    s.add(Sum(stuttgart_days) >= 1)
    
    # Total days per city
    man_days = Sum([If(day_to_city[i] == city_map[man], 1, 0) for i in range(15)])
    stut_days = Sum([If(day_to_city[i] == city_map[stut], 1, 0) for i in range(15)])
    mad_days = Sum([If(day_to_city[i] == city_map[mad], 1, 0) for i in range(15)])
    vie_days = Sum([If(day_to_city[i] == city_map[vie], 1, 0) for i in range(15)])
    
    s.add(man_days == 7)
    s.add(stut_days == 5)
    s.add(mad_days == 4)
    s.add(vie_days == 2)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 16):
            city_num = model.evaluate(day_to_city[day-1]).as_long()
            city_name = inv_city_map[city_num]
            itinerary.append({'day': day, 'place': city_name})
        
        # Prepare the output
        output = {
            'itinerary': itinerary
        }
        return output
    else:
        return None

# Execute and print the result
result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")