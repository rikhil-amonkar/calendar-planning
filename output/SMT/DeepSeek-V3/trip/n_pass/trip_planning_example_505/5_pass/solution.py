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
    city_list = list(cities.keys())
    city_map = {city: idx for idx, city in enumerate(city_list)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Stuttgart', 'Split'),
        ('Stuttgart', 'Krakow'),
        ('Prague', 'Florence'),
        ('Prague', 'Split'),
        ('Prague', 'Krakow'),
        ('Krakow', 'Split')
    ]
    
    # Days: 1 to 8
    days = 8
    
    s = Solver()
    
    # Create variables: for each day, which city we're in
    location = [Int(f'loc_{day}') for day in range(days)]
    for day in range(days):
        s.add(location[day] >= 0, location[day] < len(city_list))
    
    # Flight transitions between days
    for day in range(days - 1):
        current = location[day]
        next_ = location[day + 1]
        # Either stay in same city or take a direct flight
        s.add(Or(
            current == next_,
            *[And(current == city_map[c1], next_ == city_map[c2]) 
              for (c1, c2) in direct_flights],
            *[And(current == city_map[c2], next_ == city_map[c1]) 
              for (c1, c2) in direct_flights]
        ))
    
    # Count days in each city (including flight days)
    for city, req_days in cities.items():
        count = Sum([If(location[day] == city_map[city], 1, 0) for day in range(days)])
        s.add(count == req_days)
    
    # Wedding in Stuttgart between day 2-3 (1-based)
    s.add(Or(
        location[1] == city_map['Stuttgart'],  # Day 2
        location[2] == city_map['Stuttgart']   # Day 3
    ))
    
    # Meeting in Split between day 3-4 (1-based)
    s.add(Or(
        location[2] == city_map['Split'],  # Day 3
        location[3] == city_map['Split']   # Day 4
    ))
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(days):
            city_idx = model.eval(location[day]).as_long()
            itinerary.append({
                'day': day + 1,
                'place': city_list[city_idx]
            })
        
        # Verify flight days are counted for both cities
        for day in range(days - 1):
            if model.eval(location[day]) != model.eval(location[day + 1]):
                itinerary[day]['place'] += f" (flight to {itinerary[day + 1]['place']})"
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")