from z3 import *

def main():
    cities = {
        0: 'Berlin',
        1: 'Nice',
        2: 'Athens',
        3: 'Stockholm',
        4: 'Barcelona',
        5: 'Vilnius',
        6: 'Lyon'
    }
    required_days = [3, 5, 5, 5, 2, 4, 2]  # Berlin, Nice, Athens, Stockholm, Barcelona, Vilnius, Lyon
    
    allowed_flights = [
        (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
        (1, 2), (1, 3), (1, 4), (1, 6),
        (2, 3), (2, 4), (2, 5),
        (3, 4),
        (4, 6)
    ]
    
    s = Solver()
    c = [Int('c_%d' % i) for i in range(20)]
    
    for i in range(20):
        s.add(And(c[i] >= 0, c[i] <= 6))
    
    def flight_ok(a, b):
        return Or([Or(And(a == x, b == y), And(a == y, b == x)] for (x, y) in allowed_flights)
    
    s.add(c[0] == 0)
    s.add(c[1] == 0)
    
    for i in range(1, 20):
        s.add(Implies(c[i] != c[i-1], flight_ok(c[i-1], c[i])))
    
    moves = [If(c[i] != c[i-1], 1, 0) for i in range(1, 20)]
    s.add(sum(moves) == 6)
    
    for city_idx in range(7):
        total_days = 0
        for day in range(20):
            if day == 0:
                total_days += If(c[day] == city_idx, 1, 0)
            else:
                total_days += If(Or(c[day-1] == city_idx, c[day] == city_idx), 1, 0)
        s.add(total_days == required_days[city_idx])
    
    s.add(c[0] == 0)
    s.add(Or(c[1] == 0, c[2] == 0))
    s.add(Or(c[1] == 4, c[2] == 4))
    s.add(Or(c[2] == 4, c[3] == 4))
    s.add(Or(c[2] == 6, c[3] == 6))
    s.add(Or(c[3] == 6, c[4] == 6))
    
    if s.check() == sat:
        m = s.model()
        c_vals = [m.evaluate(c[i]) for i in range(20)]
        c_vals_int = [c_val.as_long() for c_val in c_vals]
        
        daily_sets = []
        daily_sets.append({c_vals_int[0]})
        daily_sets.append({c_vals_int[1]})
        
        for i in range(2, 20):
            if c_vals_int[i] == c_vals_int[i-1]:
                daily_sets.append({c_vals_int[i]})
            else:
                daily_sets.append({c_vals_int[i-1], c_vals_int[i]})
        
        for day_idx, cities_set in enumerate(daily_sets):
            city_names = sorted([cities[city] for city in cities_set])
            print(f"Day {day_idx+1}: {', '.join(city_names)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()