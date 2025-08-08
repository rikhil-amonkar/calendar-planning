from z3 import *
import json

def main():
    cities = ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw']
    days = list(range(1, 21))
    
    connections = [
        ('Florence', 'Vienna'),
        ('Paris', 'Warsaw'),
        ('Munich', 'Vienna'),
        ('Porto', 'Vienna'),
        ('Warsaw', 'Vienna'),
        ('Florence', 'Munich'),
        ('Munich', 'Warsaw'),
        ('Munich', 'Nice'),
        ('Paris', 'Florence'),
        ('Warsaw', 'Nice'),
        ('Porto', 'Munich'),
        ('Porto', 'Nice'),
        ('Paris', 'Vienna'),
        ('Nice', 'Vienna'),
        ('Porto', 'Paris'),
        ('Paris', 'Nice'),
        ('Paris', 'Munich'),
        ('Porto', 'Warsaw')
    ]
    
    normalized_connections = set()
    for a, b in connections:
        if a < b:
            normalized_connections.add((a, b))
        else:
            normalized_connections.add((b, a))
    
    solver = Solver()
    x = {}
    for day in days:
        for city in cities:
            x[(day, city)] = Bool(f'x_{day}_{city}')
    
    # Fixed stays: Porto (days 1-3), Warsaw (days 13-15), Vienna (days 19-20)
    for day in [1, 2, 3]:
        solver.add(x[(day, 'Porto')])
    for day in range(4, 21):
        solver.add(Not(x[(day, 'Porto')]))
    
    for day in [13, 14, 15]:
        solver.add(x[(day, 'Warsaw')])
    for day in list(range(1, 13)) + list(range(16, 21)):
        solver.add(Not(x[(day, 'Warsaw')]))
    
    for day in [19, 20]:
        solver.add(x[(day, 'Vienna')])
    for day in range(1, 19):
        solver.add(Not(x[(day, 'Vienna')]))
    
    # Exclusive days: only one city on days 1, 2, 14, 20
    for day in [1, 2]:
        for city in cities:
            if city != 'Porto':
                solver.add(Not(x[(day, city)]))
    for day in [14]:
        for city in cities:
            if city != 'Warsaw':
                solver.add(Not(x[(day, city)]))
    for day in [20]:
        for city in cities:
            if city != 'Vienna':
                solver.add(Not(x[(day, city)]))
    
    # Total days per city
    solver.add(Sum([If(x[(d, 'Paris')], 1, 0) for d in days]) == 5)
    solver.add(Sum([If(x[(d, 'Florence')], 1, 0) for d in days]) == 3)
    solver.add(Sum([If(x[(d, 'Munich')], 1, 0) for d in days]) == 5)
    solver.add(Sum([If(x[(d, 'Nice')], 1, 0) for d in days]) == 5)
    
    # Total city-days must be 26 (20 days + 6 flight days)
    total_city_days = Sum([If(x[(d, c)], 1, 0) for d in days for c in cities])
    solver.add(total_city_days == 26)
    
    # Flight days: exactly 6 days with two cities
    two_city_days = []
    for day in days:
        city_vars = [x[(day, c)] for c in cities]
        cond = (Sum([If(v, 1, 0) for v in city_vars]) == 2)
        two_city_days.append(If(cond, 1, 0))
    solver.add(Sum(two_city_days) == 6)
    
    # Mandatory flight days: days 3, 13, 15, 19 must have exactly two cities
    for day in [3, 13, 15, 19]:
        city_vars = [x[(day, c)] for c in cities]
        solver.add(Sum([If(v, 1, 0) for v in city_vars]) == 2)
    
    # Connection constraints: only connected cities can coexist
    for day in days:
        for c1 in cities:
            for c2 in cities:
                if c1 < c2:
                    if (c1, c2) not in normalized_connections:
                        solver.add(Not(And(x[(day, c1)], x[(day, c2)])))
    
    # Consecutive days must share at least one city
    for day in range(1, 20):
        common_city = Or([And(x[(day, c)], x[(day+1, c)]) for c in cities])
        solver.add(common_city)
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in days:
            for city in cities:
                if is_true(model.eval(x[(day, city)])):
                    itinerary.append({"day": day, "city": city})
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()