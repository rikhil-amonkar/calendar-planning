from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Naples', 'Valencia', 'Stuttgart', 'Split', 'Venice', 'Amsterdam', 'Nice', 'Barcelona', 'Porto']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (from the problem statement)
    flight_pairs = [
        ('Venice', 'Nice'), ('Naples', 'Amsterdam'), ('Barcelona', 'Nice'),
        ('Amsterdam', 'Nice'), ('Stuttgart', 'Valencia'), ('Stuttgart', 'Porto'),
        ('Split', 'Stuttgart'), ('Split', 'Naples'), ('Valencia', 'Amsterdam'),
        ('Barcelona', 'Porto'), ('Valencia', 'Naples'), ('Venice', 'Amsterdam'),
        ('Barcelona', 'Naples'), ('Barcelona', 'Valencia'), ('Split', 'Amsterdam'),
        ('Barcelona', 'Venice'), ('Stuttgart', 'Amsterdam'), ('Naples', 'Nice'),
        ('Venice', 'Stuttgart'), ('Split', 'Barcelona'), ('Porto', 'Nice'),
        ('Barcelona', 'Stuttgart'), ('Venice', 'Naples'), ('Porto', 'Amsterdam'),
        ('Porto', 'Valencia'), ('Stuttgart', 'Naples'), ('Barcelona', 'Amsterdam')
    ]
    
    # Build adjacency list
    adjacency = {city: set() for city in cities}
    for a, b in flight_pairs:
        adjacency[a].add(b)
        adjacency[b].add(a)
    
    # Create solver
    s = Solver()
    
    # Variables: city each day (1..24)
    days = 24
    city_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Each day's city must be valid
    for var in city_vars:
        s.add(var >= 0, var < len(cities))
    
    # Constraint: consecutive days must be same city or connected by direct flight
    for i in range(days - 1):
        current = city_vars[i]
        next_ = city_vars[i + 1]
        s.add(Or(
            current == next_,
            *[And(current == city_to_idx[a], next_ == city_to_idx[b]) for a in cities for b in adjacency[a]]
        ))
    
    # Duration constraints
    durations = {
        'Naples': 3,
        'Valencia': 5,
        'Stuttgart': 2,
        'Split': 5,
        'Venice': 5,
        'Amsterdam': 4,
        'Nice': 2,
        'Barcelona': 2,
        'Porto': 4
    }
    
    for city, duration in durations.items():
        s.add(Sum([If(city_vars[i] == city_to_idx[city], 1, 0) for i in range(days)]) == duration)
    
    # Event constraints
    # Conference in Venice between day 6 and day 10 (inclusive) (5 days)
    # So days 6-10 must be Venice. But Venice total is 5 days. So these days must be consecutive.
    s.add(And(*[city_vars[i] == city_to_idx['Venice'] for i in range(5, 10)]))
    
    # Workshop in Barcelona between day 5 and day 6 (2 days)
    s.add(And(city_vars[4] == city_to_idx['Barcelona'], city_vars[5] == city_to_idx['Barcelona']))
    
    # Meet friend in Naples between day 18 and day 20 (3 days total, but Naples total is 3)
    # So at least one day in 18-20 must be Naples.
    s.add(Or(*[city_vars[i] == city_to_idx['Naples'] for i in range(17, 20)]))
    
    # Meet friends in Nice between day 23 and day 24 (2 days)
    s.add(And(city_vars[22] == city_to_idx['Nice'], city_vars[23] == city_to_idx['Nice']))
    
    # Check solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(days):
            city_idx = m.evaluate(city_vars[day]).as_long()
            itinerary.append({'day': day + 1, 'city': cities[city_idx]})
        
        # Verify the itinerary meets all constraints
        # (For brevity, assume the solver's model is correct)
        
        return json.dumps({'itinerary': itinerary}, indent=2)
    else:
        return json.dumps({'error': 'No solution found'})

print(solve_itinerary())