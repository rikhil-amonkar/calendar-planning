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
    
    # 21 variables for 20 days (c1 to c21)
    c = [Const(f'c_{i}', City) for i in range(1, 22)]
    
    s = Solver()
    
    # Flight constraints
    for i in range(20):
        stay = c[i] == c[i+1]
        flight = Or([And(c[i] == a, c[i+1] == b) for (a, b) in allowed_edges])
        s.add(Or(stay, flight))
    
    # Total days per city
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
    
    # Fixed events with stricter constraints
    # Oslo: full days on 16 and 17 (no travel)
    s.add(c[15] == City.Oslo, c[16] == City.Oslo)  # Start and end of day 16
    s.add(c[16] == City.Oslo, c[17] == City.Oslo)  # Start and end of day 17
    
    # Reykjavik: at least one full day between 9-13
    reyk_constraints = []
    for d in range(8, 13):  # Days 9-13
        reyk_constraints.append(And(c[d] == City.Reykjavik, c[d+1] == City.Reykjavik))
    s.add(Or(reyk_constraints))
    
    # Munich: full days during 13-16
    munich_constraints = []
    for d in range(12, 16):  # Days 13-16
        munich_constraints.append(And(c[d] == City.Munich, c[d+1] == City.Munich))
    s.add(Or(munich_constraints))
    
    # Frankfurt: full days during 17-20
    frankfurt_constraints = []
    for d in range(16, 20):  # Days 17-20
        frankfurt_constraints.append(And(c[d] == City.Frankfurt, c[d+1] == City.Frankfurt))
    s.add(Or(frankfurt_constraints))
    
    # Block previous invalid solution
    prev_solution = [
        City.Split, City.Split, City.Split, City.Stockholm, City.Stockholm, 
        City.Stockholm, City.Barcelona, City.Barcelona, City.Reykjavik, 
        City.Reykjavik, City.Reykjavik, City.Reykjavik, City.Munich, 
        City.Munich, City.Munich, City.Bucharest, City.Oslo, City.Frankfurt,
        City.Frankfurt, City.Frankfurt, City.Frankfurt
    ]
    s.add(Not(And(*[c[i] == prev_solution[i] for i in range(21)])))
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i in range(20):
            start = m.eval(c[i])
            end = m.eval(c[i+1])
            if start == end:
                schedule.append(f"Day {i+1}: Stay in {start}")
            else:
                schedule.append(f"Day {i+1}: Travel from {start} to {end} (thus in both {start} and {end})")
        print("Found a valid trip plan:")
        for entry in schedule:
            print(entry)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()