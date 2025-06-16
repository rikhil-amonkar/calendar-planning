from z3 import *

def main():
    city_names = ['London', 'Zurich', 'Bucharest', 'Hamburg', 'Barcelona', 'Reykjavik', 'Stuttgart', 'Stockholm', 'Tallinn', 'Milan']
    
    flights_list = [
        ('London', 'Hamburg'),
        ('London', 'Reykjavik'),
        ('Milan', 'Barcelona'),
        ('Reykjavik', 'Barcelona'),
        ('Reykjavik', 'Stuttgart'),
        ('Stockholm', 'Reykjavik'),
        ('London', 'Stuttgart'),
        ('Milan', 'Zurich'),
        ('London', 'Barcelona'),
        ('Stockholm', 'Hamburg'),
        ('Zurich', 'Barcelona'),
        ('Stockholm', 'Stuttgart'),
        ('Milan', 'Hamburg'),
        ('Stockholm', 'Tallinn'),
        ('Hamburg', 'Bucharest'),
        ('London', 'Bucharest'),
        ('Milan', 'Stockholm'),
        ('Stuttgart', 'Hamburg'),
        ('London', 'Zurich'),
        ('Milan', 'Reykjavik'),
        ('London', 'Stockholm'),
        ('Milan', 'Stuttgart'),
        ('Stockholm', 'Barcelona'),
        ('London', 'Milan'),
        ('Zurich', 'Hamburg'),
        ('Bucharest', 'Barcelona'),
        ('Zurich', 'Stockholm'),
        ('Barcelona', 'Tallinn'),
        ('Zurich', 'Tallinn'),
        ('Hamburg', 'Barcelona'),
        ('Stuttgart', 'Barcelona'),
        ('Zurich', 'Reykjavik'),
        ('Zurich', 'Bucharest')
    ]
    
    required_days_dict = {
        'London': 3,
        'Zurich': 2,
        'Bucharest': 2,
        'Hamburg': 5,
        'Barcelona': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Stockholm': 2,
        'Tallinn': 4,
        'Milan': 5
    }
    
    City = Datatype('City')
    for name in city_names:
        City.declare(name)
    City = City.create()
    
    city_enum = {name: getattr(City, name) for name in city_names}
    
    neighbors = {name: set() for name in city_names}
    for (A, B) in flights_list:
        if A in city_names and B in city_names:
            neighbors[A].add(B)
            neighbors[B].add(A)
    
    allowed_next_enum = {}
    for name in city_names:
        allowed_next_enum[city_enum[name]] = [city_enum[n] for n in [name] + list(neighbors[name])]
    
    city_start = [None]
    for i in range(1, 30):
        city_start.append(Const(f'city_start_{i}', City))
    
    s = Solver()
    
    s.add(city_start[1] == city_enum['London'])
    s.add(city_start[2] == city_enum['London'])
    s.add(city_start[3] == city_enum['London'])
    
    s.add(city_start[7] == city_enum['Zurich'])
    s.add(city_start[8] == city_enum['Zurich'])
    
    for d in range(10, 14):
        s.add(Or(city_start[d] == city_enum['Reykjavik'], city_start[d+1] == city_enum['Reykjavik']))
    
    for d in range(1, 29):
        for c_enum in [city_enum[name] for name in city_names]:
            s.add(Implies(city_start[d] == c_enum, 
                          Or([city_start[d+1] == next_city for next_city in allowed_next_enum[c_enum]])))
    
    milan_constraints = []
    for d in range(3, 8):
        milan_constraints.append(Or(city_start[d] == city_enum['Milan'], city_start[d+1] == city_enum['Milan']))
    s.add(Or(milan_constraints))
    
    for c in city_names:
        total = 0
        for d in range(1, 29):
            in_day = Or(city_start[d] == city_enum[c], city_start[d+1] == city_enum[c])
            total += If(in_day, 1, 0)
        s.add(total == required_days_dict[c])
    
    if s.check() == sat:
        m = s.model()
        for d in range(1, 29):
            c1 = m.eval(city_start[d])
            c2 = m.eval(city_start[d+1])
            if c1.eq(c2):
                print(f"Day {d}: {c1}")
            else:
                print(f"Day {d}: {c1} and {c2}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()