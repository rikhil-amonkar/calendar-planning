from z3 import *
import json

def main():
    # Define the cities and their required stay durations
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    req_days = {
        'Porto': 2,
        'Geneva': 3,
        'Mykonos': 3,
        'Manchester': 4,
        'Hamburg': 5,
        'Naples': 5,
        'Frankfurt': 2
    }
    
    # Define direct flight connections as bidirectional edges
    edges_str = [
        ('Hamburg', 'Frankfurt'),
        ('Naples', 'Mykonos'),
        ('Hamburg', 'Porto'),
        ('Hamburg', 'Geneva'),
        ('Mykonos', 'Geneva'),
        ('Frankfurt', 'Geneva'),
        ('Frankfurt', 'Porto'),
        ('Geneva', 'Porto'),
        ('Geneva', 'Manchester'),
        ('Naples', 'Manchester'),
        ('Frankfurt', 'Naples'),
        ('Frankfurt', 'Manchester'),
        ('Naples', 'Geneva'),
        ('Porto', 'Manchester'),
        ('Hamburg', 'Manchester')
    ]
    
    # Create Z3 enum type for cities
    City = Datatype('City')
    for c in cities:
        City.declare(c)
    City = City.create()
    
    # Map city names to Z3 constants
    city_constants = {name: getattr(City, name) for name in cities}
    
    # Create set of allowed flight moves (bidirectional edges and same-city stays)
    edge_set = set()
    for a, b in edges_str:
        a_const = city_constants[a]
        b_const = city_constants[b]
        edge_set.add((a_const, b_const))
        edge_set.add((b_const, a_const))
    
    # Add same-city moves (no flight)
    same_city_set = {(city_constants[c], city_constants[c]) for c in cities}
    allowed_set = edge_set.union(same_city_set)
    
    # Create Z3 solver and variables
    s = [Const(f's_{i}', City) for i in range(19)]
    solver = Solver()
    
    # Constraint: Total days in each city
    for city_name in cities:
        c = city_constants[city_name]
        total = 0
        for d in range(1, 19):  # Days 1 to 18
            total += If(Or(s[d-1] == c, s[d] == c), 1, 0)
        solver.add(total == req_days[city_name])
    
    # Constraint: Mykonos between days 10-12
    mykonos = city_constants['Mykonos']
    solver.add(Or(
        Or(s[9] == mykonos, s[10] == mykonos),
        Or(s[10] == mykonos, s[11] == mykonos),
        Or(s[11] == mykonos, s[12] == mykonos)
    ))
    
    # Constraint: Manchester between days 15-18
    manchester = city_constants['Manchester']
    solver.add(Or(
        Or(s[14] == manchester, s[15] == manchester),
        Or(s[15] == manchester, s[16] == manchester),
        Or(s[16] == manchester, s[17] == manchester),
        Or(s[17] == manchester, s[18] == manchester)
    ))
    
    # Constraint: Frankfurt on days 5 and 6
    frankfurt = city_constants['Frankfurt']
    solver.add(Or(s[4] == frankfurt, s[5] == frankfurt))
    solver.add(Or(s[5] == frankfurt, s[6] == frankfurt))
    
    # Constraint: Consecutive cities must be connected by a direct flight or the same
    for i in range(18):
        solver.add(Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_set]))
    
    # Solve and output itinerary if solution exists
    if solver.check() == sat:
        model = solver.model()
        s_val = [model.eval(s_i) for s_i in s]
        
        itinerary = []
        for day in range(1, 19):
            start_city = s_val[day-1]
            end_city = s_val[day]
            start_name = start_city.decl().name()
            end_name = end_city.decl().name()
            itinerary.append({"day": day, "city": start_name})
            if start_name != end_name:
                itinerary.append({"day": day, "city": end_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()