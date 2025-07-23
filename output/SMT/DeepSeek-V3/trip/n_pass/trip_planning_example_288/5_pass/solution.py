from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flight connections
    connections = {
        'Manchester': ['Stuttgart', 'Madrid', 'Vienna'],
        'Stuttgart': ['Manchester', 'Vienna'],
        'Madrid': ['Manchester', 'Vienna'],
        'Vienna': ['Manchester', 'Stuttgart', 'Madrid']
    }
    
    # Total days
    total_days = 15
    
    # Create Z3 variables for each day
    day_vars = [Int(f'day_{i}') for i in range(total_days)]
    
    s = Solver()
    
    # Each day must be assigned to a valid city
    for day in day_vars:
        s.add(day >= 0, day < len(cities))
    
    # Manchester must be days 1-7 (indexes 0-6)
    for i in range(7):
        s.add(day_vars[i] == city_idx['Manchester'])
    
    # Stuttgart must include at least one day between 11-15 (indexes 10-14)
    s.add(Or([day_vars[i] == city_idx['Stuttgart'] for i in range(10, 15)]))
    
    # Total days per city
    city_days = [
        ('Manchester', 7),
        ('Stuttgart', 5),
        ('Madrid', 4),
        ('Vienna', 2)
    ]
    
    for city, days in city_days:
        s.add(Sum([If(day_vars[i] == city_idx[city], 1, 0) for i in range(total_days)]) == days)
    
    # Flight constraints
    for i in range(total_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        # Either stay in same city or take direct flight
        s.add(Or(
            current == next_day,
            And(
                current != next_day,
                Or([And(current == city_idx[city], next_day == city_idx[adj]) 
                    for city in cities 
                    for adj in connections[city]])
            )
        ))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(total_days):
            city = cities[model.eval(day_vars[i]).as_long()]
            itinerary.append({'day': i + 1, 'place': city})
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(result)
else:
    print("No valid itinerary found.")