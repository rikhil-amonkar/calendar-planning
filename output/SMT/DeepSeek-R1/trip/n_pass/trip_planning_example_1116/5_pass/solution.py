from z3 import *

def main():
    City = Datatype('City')
    cities = ['Oslo', 'Reykjavik', 'Stockholm', 'Munich', 'Frankfurt', 'Barcelona', 'Bucharest', 'Split']
    for city in cities:
        City.declare(city)
    City = City.create()
    
    direct_flights = [
        ('Reykjavik', 'Munich'), ('Munich', 'Frankfurt'), ('Split', 'Oslo'), 
        ('Reykjavik', 'Oslo'), ('Bucharest', 'Munich'), ('Oslo', 'Frankfurt'), 
        ('Bucharest', 'Barcelona'), ('Barcelona', 'Frankfurt'), ('Reykjavik', 'Frankfurt'), 
        ('Barcelona', 'Stockholm'), ('Barcelona', 'Reykjavik'), ('Stockholm', 'Reykjavik'), 
        ('Barcelona', 'Split'), ('Bucharest', 'Oslo'), ('Bucharest', 'Frankfurt'), 
        ('Split', 'Stockholm'), ('Barcelona', 'Oslo'), ('Stockholm', 'Munich'), 
        ('Stockholm', 'Oslo'), ('Split', 'Frankfurt'), ('Barcelona', 'Munich'), 
        ('Stockholm', 'Frankfurt'), ('Munich', 'Oslo'), ('Split', 'Munich')
    ]
    allowed_edges = []
    for a, b in direct_flights:
        city_a = getattr(City, a)
        city_b = getattr(City, b)
        allowed_edges.append((city_a, city_b))
        allowed_edges.append((city_b, city_a))
    
    c = [Const(f'c_{i}', City) for i in range(21)]
    
    s = Solver()
    
    for i in range(20):
        stay = c[i] == c[i+1]
        flight_options = []
        for (a, b) in allowed_edges:
            flight_options.append(And(c[i] == a, c[i+1] == b))
        s.add(Or(stay, Or(flight_options)))
    
    total_days = {city: 0 for city in cities}
    for i in range(20):
        for city in cities:
            city_val = getattr(City, city)
            total_days[city] += If(Or(c[i] == city_val, c[i+1] == city_val), 1, 0)
    
    s.add(total_days['Oslo'] == 2)
    s.add(total_days['Reykjavik'] == 5)
    s.add(total_days['Stockholm'] == 4)
    s.add(total_days['Munich'] == 4)
    s.add(total_days['Frankfurt'] == 4)
    s.add(total_days['Barcelona'] == 3)
    s.add(total_days['Bucharest'] == 2)
    s.add(total_days['Split'] == 3)
    
    Oslo = City.Oslo
    s.add(Or(c[15] == Oslo, c[16] == Oslo))
    s.add(Or(c[16] == Oslo, c[17] == Oslo))
    
    Reykjavik = City.Reykjavik
    reyk_full_days = []
    for i in [9, 10, 11]:
        reyk_full_days.append(And(c[i] == Reykjavik, c[i+1] == Reykjavik))
    s.add(Or(reyk_full_days))
    
    Munich = City.Munich
    munich_full_days = []
    for i in [13, 14]:
        munich_full_days.append(And(c[i] == Munich, c[i+1] == Munich))
    s.add(Or(munich_full_days))
    
    Frankfurt = City.Frankfurt
    frankfurt_full_days = []
    for i in [17, 18]:
        frankfurt_full_days.append(And(c[i] == Frankfurt, c[i+1] == Frankfurt))
    s.add(Or(frankfurt_full_days))
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i in range(20):
            start = m.eval(c[i])
            end = m.eval(c[i+1])
            start_city = [k for k in cities if getattr(City, k) == start][0]
            end_city = [k for k in cities if getattr(City, k) == end][0]
            if start == end:
                schedule.append(f"Day {i+1}: Stay in {start_city}")
            else:
                schedule.append(f"Day {i+1}: Travel from {start_city} to {end_city} (thus in both {start_city} and {end_city})")
        print("Found a valid trip plan:")
        for entry in schedule:
            print(entry)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()