from z3 import *

def main():
    cities_str = ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Madrid', 'Helsinki', 'Split', 'London']
    
    flights_str = [
        ('Helsinki', 'London'),
        ('Split', 'Madrid'),
        ('Helsinki', 'Madrid'),
        ('London', 'Madrid'),
        ('Brussels', 'London'),
        ('Bucharest', 'London'),
        ('Brussels', 'Bucharest'),
        ('Bucharest', 'Madrid'),
        ('Split', 'Helsinki'),
        ('Mykonos', 'Madrid'),
        ('Stuttgart', 'London'),
        ('Helsinki', 'Brussels'),
        ('Brussels', 'Madrid'),
        ('Split', 'London'),
        ('Stuttgart', 'Split'),
        ('London', 'Mykonos')
    ]
    
    City = Datatype('City')
    for c in cities_str:
        City.declare(c)
    City = City.create()
    
    city_dict = {}
    for c in cities_str:
        city_dict[c] = getattr(City, c)
    
    flight_pairs = []
    for (a, b) in flights_str:
        flight_pairs.append((city_dict[a], city_dict[b]))
        flight_pairs.append((city_dict[b], city_dict[a]))
    
    x = [Const('x_%d' % i, City) for i in range(21)]
    
    s = Solver()
    
    for i in range(20):
        s.add(If(x[i] != x[i + 1],
                 Or([And(x[i] == a, x[i + 1] == b) for (a, b) in flight_pairs]),
                 True))
    
    def total_days(c):
        total = 0
        for i in range(20):
            total += If(x[i] == c, 1, 0)
            total += If(And(x[i] != x[i + 1], x[i + 1] == c), 1, 0)
        total += If(x[20] == c, 1, 0)
        return total
    
    s.add(total_days(city_dict['Brussels']) == 4)
    s.add(total_days(city_dict['Bucharest']) == 3)
    s.add(total_days(city_dict['Stuttgart']) == 4)
    s.add(total_days(city_dict['Mykonos']) == 2)
    s.add(total_days(city_dict['Madrid']) == 2)
    s.add(total_days(city_dict['Helsinki']) == 5)
    s.add(total_days(city_dict['Split']) == 3)
    s.add(total_days(city_dict['London']) == 5)
    
    s.add(x[20] == city_dict['Madrid'])
    
    stuttgart = city_dict['Stuttgart']
    stuttgart_constraints = []
    for i in range(4):
        stuttgart_constraints.append(x[i] == stuttgart)
        stuttgart_constraints.append(And(x[i] != x[i + 1], x[i + 1] == stuttgart))
    s.add(Or(stuttgart_constraints))
    
    if s.check() == sat:
        m = s.model()
        res = [m.eval(x_i) for x_i in x]
        city_names = {city_dict[c]: c for c in cities_str}
        for i in range(21):
            day = i + 1
            city = city_names[res[i]]
            print(f"Day {day}: {city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()