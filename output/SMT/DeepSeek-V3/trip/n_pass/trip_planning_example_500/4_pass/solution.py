from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Hamburg', 'Munich', 'Manchester', 'Lyon', 'Split']
    city_to_int = {city: i for i, city in enumerate(cities)}
    int_to_city = {i: city for i, city in enumerate(cities)}
    
    # Direct flights (undirected)
    direct_flights = [
        ('Split', 'Munich'),
        ('Munich', 'Manchester'),
        ('Hamburg', 'Manchester'),
        ('Hamburg', 'Munich'),
        ('Split', 'Lyon'),
        ('Lyon', 'Munich'),
        ('Hamburg', 'Split'),
        ('Manchester', 'Split')
    ]
    # Create an adjacency list
    adjacency = {i: set() for i in range(len(cities))}
    for a, b in direct_flights:
        a_idx = city_to_int[a]
        b_idx = city_to_int[b]
        adjacency[a_idx].add(b_idx)
        adjacency[b_idx].add(a_idx)
    
    # Create Z3 variables: day 1..20, each is a city (0..4)
    s = Solver()
    day_vars = [Int(f'day_{i}') for i in range(1, 21)]
    for var in day_vars:
        s.add(var >= 0, var < len(cities))
    
    # Constraints for fixed days
    # Manchester on days 19, 20 (indices 18, 19)
    s.add(day_vars[18] == city_to_int['Manchester'])
    s.add(day_vars[19] == city_to_int['Manchester'])
    # Lyon on days 13, 14 (indices 12, 13)
    s.add(day_vars[12] == city_to_int['Lyon'])
    s.add(day_vars[13] == city_to_int['Lyon'])
    
    # Constraints for transitions: consecutive days must be same city or adjacent
    for i in range(19):
        current = day_vars[i]
        next_day = day_vars[i+1]
        # Generate adjacency conditions
        adjacent_conditions = []
        for a in range(len(cities)):
            for b in adjacency[a]:
                adjacent_conditions.append(And(current == a, next_day == b))
        s.add(Or(current == next_day, *adjacent_conditions))
    
    # Constraints for total days per city
    # Hamburg: 7 days
    s.add(Sum([If(var == city_to_int['Hamburg'], 1, 0) for var in day_vars]) == 7)
    # Munich: 6 days
    s.add(Sum([If(var == city_to_int['Munich'], 1, 0) for var in day_vars]) == 6)
    # Manchester: 2 days (19-20)
    s.add(Sum([If(var == city_to_int['Manchester'], 1, 0) for var in day_vars]) == 2)
    # Lyon: 2 days (13-14)
    s.add(Sum([If(var == city_to_int['Lyon'], 1, 0) for var in day_vars]) == 2)
    # Split: 7 days
    s.add(Sum([If(var == city_to_int['Split'], 1, 0) for var in day_vars]) == 7)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(20):
            day = i + 1
            city_idx = model.evaluate(day_vars[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({'day': day, 'city': city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))