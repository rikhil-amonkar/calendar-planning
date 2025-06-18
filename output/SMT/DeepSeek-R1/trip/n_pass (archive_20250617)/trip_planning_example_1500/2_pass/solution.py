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
    
    # Fixed constraints for London (days 1,2,3)
    s.add(city_start[1] == city_enum['London'])
    s.add(city_start[2] == city_enum['London'])
    s.add(city_start[3] == city_enum['London'])
    # For day 1: entire day in London -> city_start[1] and [2] are London (already set)
    # For day 2: entire day in London -> city_start[2] and [3] are London (already set)
    # For day 3: start in London, and we can fly away during the day -> so only set start of day 3 to London (already set). The flight will be handled by the transition constraint.

    # Fixed constraints for Zurich (days 7,8)
    s.add(city_start[7] == city_enum['Zurich'])
    s.add(city_start[8] == city_enum['Zurich'])
    # For day 7: entire day in Zurich -> city_start[7] and [8] are Zurich (already set)
    # For day 8: start in Zurich, and we can fly away during the day -> only set start of day 8 to Zurich (already set).

    # Fixed constraints for Reykjavik (days 9-13)
    s.add(city_start[9] == city_enum['Reykjavik'])
    s.add(city_start[10] == city_enum['Reykjavik'])
    s.add(city_start[11] == city_enum['Reykjavik'])
    s.add(city_start[12] == city_enum['Reykjavik'])
    s.add(city_start[13] == city_enum['Reykjavik'])
    # For day 9: entire day -> city_start[9] and [10] are Reykjavik (set above)
    # For day 10: entire day -> city_start[10] and [11] are Reykjavik (set above)
    # For day 11: entire day -> city_start[11] and [12] are Reykjavik (set above)
    # For day 12: entire day -> city_start[12] and [13] are Reykjavik (set above)
    # For day 13: start in Reykjavik, and we can fly away during the day -> only set start of day 13 to Reykjavik (already set).
    
    # Constraints for transitions (flights)
    for d in range(1, 29):
        for c_enum in [city_enum[name] for name in city_names]:
            s.add(Implies(city_start[d] == c_enum, 
                          Or([city_start[d+1] == next_city for next_city in allowed_next_enum[c_enum]])))
    
    # Constraints for not being in fixed cities on other days
    for d in range(1, 29):
        if d not in [1,2,3]:
            # For London: not on any other day
            s.add(Not(Or(city_start[d] == city_enum['London'], city_start[d+1] == city_enum['London'])))
        if d not in [7,8]:
            # For Zurich: not on any other day
            s.add(Not(Or(city_start[d] == city_enum['Zurich'], city_start[d+1] == city_enum['Zurich'])))
        if d not in [9,10,11,12,13]:
            # For Reykjavik: not on any other day
            s.add(Not(Or(city_start[d] == city_enum['Reykjavik'], city_start[d+1] == city_enum['Reykjavik'])))
    
    # Meeting in Milan between days 3 and 7 (inclusive)
    milan_constraints = []
    for d in range(3, 8):
        milan_constraints.append(Or(city_start[d] == city_enum['Milan'], city_start[d+1] == city_enum['Milan']))
    s.add(Or(milan_constraints))
    
    # Total days per city
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