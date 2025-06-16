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
    city_dict = {c: getattr(City, c) for c in cities_str}
    
    flight_pairs = []
    for a, b in flights_str:
        flight_pairs.append((city_dict[a], city_dict[b]))
        flight_pairs.append((city_dict[b], city_dict[a]))
    
    s0 = Const('s0', City)
    x = [Const(f'x_{i}', City) for i in range(21)]
    
    s = Solver()
    
    flight_exists = {}
    for a, b in flight_pairs:
        flight_exists[(a, b)] = True
    
    def has_flight(a, b):
        return Or([And(a == a1, b == b1) for (a1, b1) in flight_pairs])
    
    travel_day1 = If(s0 != x[0], 1, 0)
    s.add(If(s0 != x[0], has_flight(s0, x[0]), True))
    
    travel_days = []
    for i in range(20):
        travel = If(x[i] != x[i+1], 1, 0)
        travel_days.append(travel)
        s.add(If(x[i] != x[i+1], has_flight(x[i], x[i+1]), True))
    
    def total_days(c):
        total = 0
        total += If(And(travel_day1 == 1, s0 == c), 1, 0)
        for i in range(20):
            total += If(And(travel_days[i] == 1, x[i] == c), 1, 0)
        for i in range(21):
            total += If(x[i] == c, 1, 0)
        return total
    
    s.add(total_days(city_dict['Brussels']) == 4)
    s.add(total_days(city_dict['Bucharest']) == 3)
    s.add(total_days(city_dict['Stuttgart']) == 4)
    s.add(total_days(city_dict['Mykonos']) == 2)
    s.add(total_days(city_dict['Madrid']) == 2)
    s.add(total_days(city_dict['Helsinki']) == 5)
    s.add(total_days(city_dict['Split']) == 3)
    s.add(total_days(city_dict['London']) == 5)
    
    s.add(x[19] == city_dict['Madrid'])
    s.add(x[20] == city_dict['Madrid'])
    
    stuttgart_in_first4 = Or([x[i] == city_dict['Stuttgart'] for i in range(4)])
    s.add(stuttgart_in_first4)
    
    if s.check() == sat:
        m = s.model()
        start_val = m.eval(s0)
        end_vals = [m.eval(x_i) for x_i in x]
        city_names = {getattr(City, c): c for c in cities_str}
        
        print("Day 1:", city_names[start_val])
        for i in range(21):
            print(f"Day {i+2}:", city_names[end_vals[i]])
    else:
        print("No solution found")

if __name__ == "__main__":
    main()