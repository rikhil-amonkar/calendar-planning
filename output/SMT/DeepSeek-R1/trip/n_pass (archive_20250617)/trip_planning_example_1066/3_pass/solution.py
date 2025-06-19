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
    
    s0 = Const('s0', City)  # Start city for day 1
    x = [Const(f'x_{i}', City) for i in range(21)]  # End city for each day
    
    s = Solver()
    
    # Flight constraint for day 1
    s.add(If(s0 != x[0],
             Or([And(s0 == a, x[0] == b) for (a, b) in flight_pairs]),
             True))
    
    # Flight constraints for days 2-21
    for i in range(20):
        s.add(If(x[i] != x[i+1],
                 Or([And(x[i] == a, x[i+1] == b) for (a, b) in flight_pairs]),
                 True))
    
    # Total days calculation per city
    def total_days(c):
        total = 0
        # Day 1
        total += If(s0 == c, 1, 0)  # Start of day
        total += If(And(s0 != x[0], x[0] == c), 1, 0)  # Arrival if traveled
        
        # Days 2-21
        for i in range(20):
            total += If(x[i] == c, 1, 0)  # Start of day i+2
            total += If(And(x[i] != x[i+1], x[i+1] == c), 1, 0)  # Arrival if traveled
        return total
    
    # Set total days per city
    s.add(total_days(city_dict['Brussels']) == 4)
    s.add(total_days(city_dict['Bucharest']) == 3)
    s.add(total_days(city_dict['Stuttgart']) == 4)
    s.add(total_days(city_dict['Mykonos']) == 2)
    s.add(total_days(city_dict['Madrid']) == 2)
    s.add(total_days(city_dict['Helsinki']) == 5)
    s.add(total_days(city_dict['Split']) == 3)
    s.add(total_days(city_dict['London']) == 5)
    
    # Must be in Madrid on last two days (days 20 and 21)
    s.add(x[19] == city_dict['Madrid'])  # Day 20 end
    s.add(x[20] == city_dict['Madrid'])  # Day 21 end
    
    # At least one day in Stuttgart between days 1-4
    stuttgart = city_dict['Stuttgart']
    stuttgart_days = [
        s0 == stuttgart,        # Day 1 start
        x[0] == stuttgart,       # Day 1 end
        x[1] == stuttgart,       # Day 2 end
        x[2] == stuttgart,       # Day 3 end
        x[3] == stuttgart        # Day 4 end
    ]
    s.add(Or(stuttgart_days))
    
    if s.check() == sat:
        m = s.model()
        start_day1 = m.eval(s0)
        end_days = [m.eval(x_i) for x_i in x]
        city_names = {city_dict[c]: c for c in cities_str}
        
        # Output itinerary
        print(f"Day 1 start: {city_names[start_day1]}")
        for i in range(21):
            print(f"Day {i+1} end: {city_names[end_days[i]]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()