from z3 import *

def main():
    Cities = ['Barcelona', 'Florence', 'Frankfurt', 'Salzburg', 'Stockholm', 'Stuttgart', 'Venice']
    required_days = {
        'Barcelona': 2,
        'Florence': 4,
        'Frankfurt': 4,
        'Salzburg': 4,
        'Stockholm': 2,
        'Stuttgart': 3,
        'Venice': 5
    }
    
    direct_flights_list = [
        ('Barcelona', 'Frankfurt'),
        ('Florence', 'Frankfurt'),
        ('Stockholm', 'Barcelona'),
        ('Barcelona', 'Florence'),
        ('Venice', 'Barcelona'),
        ('Stuttgart', 'Barcelona'),
        ('Frankfurt', 'Salzburg'),
        ('Stockholm', 'Frankfurt'),
        ('Stuttgart', 'Stockholm'),
        ('Stuttgart', 'Frankfurt'),
        ('Venice', 'Stuttgart'),
        ('Venice', 'Frankfurt')
    ]
    
    direct_flights_set = set()
    for (a, b) in direct_flights_list:
        direct_flights_set.add((a, b))
        direct_flights_set.add((b, a))
    
    # Get connected cities for Venice
    venice_connections = [c for c in Cities if c != 'Venice' and ('Venice', c) in direct_flights_set]
    
    s = Solver()
    
    in_city = {}
    for d in range(1, 19):
        for c in Cities:
            in_city[(d, c)] = Bool(f"in_{d}_{c}")
    
    travel = [Bool(f"travel_{d}") for d in range(1, 19)]
    
    # Cardinality constraints
    for d in range(1, 19):
        total = Sum([If(in_city[(d, c)], 1, 0) for c in Cities])
        s.add(travel[d-1] == (total == 2))
    
    # Unconnected cities constraints
    all_pairs = [(a, b) for a in Cities for b in Cities if a < b]
    unconnected_pairs = [(a, b) for (a, b) in all_pairs if (a, b) not in direct_flights_set]
    
    for d in range(1, 19):
        for (a, b) in unconnected_pairs:
            s.add(Or(Not(in_city[(d, a)]), Not(in_city[(d, b)])))
    
    # Days 1-5 in Venice
    for d in range(1, 6):
        s.add(in_city[(d, 'Venice')])
    
    # Total days per city
    for c in Cities:
        total = Sum([If(in_city[(d, c)], 1, 0) for d in range(1, 19)])
        s.add(total == required_days[c])
    
    # Continuity between days
    for d in range(1, 18):
        common = Or([And(in_city[(d, c)], in_city[(d+1, c)]) for c in Cities])
        s.add(common)
    
    # Day 5 must be travel day
    s.add(travel[4])
    
    # On day 5, must be in Venice + one connected city (but not Stuttgart)
    s.add(Or(*[in_city[(5, c)] for c in venice_connections if c != 'Stuttgart']))
    s.add(Not(in_city[(5, 'Stuttgart')]))
    
    if s.check() == sat:
        m = s.model()
        for d in range(1, 19):
            cities_on_day = [c for c in Cities if m.eval(in_city[(d, c)])]
            is_travel = m.eval(travel[d-1])
            if is_travel:
                print(f"Day {d}: Travel between {cities_on_day[0]} and {cities_on_day[1]} (in both cities)")
            else:
                print(f"Day {d}: Stay in {cities_on_day[0]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()