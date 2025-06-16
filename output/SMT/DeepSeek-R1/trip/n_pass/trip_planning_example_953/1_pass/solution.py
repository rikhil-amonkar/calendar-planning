from z3 import *

def main():
    # Define cities and their required days
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
    
    # Direct flights list
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
    
    # Create a set of direct flights in both directions
    direct_flights_set = set()
    for (a, b) in direct_flights_list:
        direct_flights_set.add((a, b))
        direct_flights_set.add((b, a))
    
    # Create Z3 solver
    s = Solver()
    
    # Create in_city variables: in_city[(day, city)]
    in_city = {}
    for d in range(1, 19):
        for c in Cities:
            in_city[(d, c)] = Bool(f"in_{d}_{c}")
    
    # Create travel variables: travel[d] for day d (1 to 18)
    travel = [ Bool(f"travel_{d}") for d in range(1, 19) ]
    
    # Constraint: For each day, if travel is True, exactly two cities are True; else, exactly one
    for d in range(1, 19):
        total = Sum([If(in_city[(d, c)], 1, 0) for c in Cities])
        s.add(travel[d-1] == (total == 2))
    
    # Generate all unordered pairs of distinct cities
    all_pairs = []
    for i in range(len(Cities)):
        for j in range(i+1, len(Cities)):
            all_pairs.append((Cities[i], Cities[j]))
    
    # Identify unconnected pairs (without direct flights)
    unconnected_pairs = []
    for (A, B) in all_pairs:
        if (A, B) not in direct_flights_set:
            unconnected_pairs.append((A, B))
    
    # Constraint: For unconnected pairs, they cannot both be True on the same day
    for d in range(1, 19):
        for (A, B) in unconnected_pairs:
            s.add(Or(Not(in_city[(d, A)]), Not(in_city[(d, B)])))
    
    # Constraint: Venice on days 1 to 5
    for d in range(1, 6):
        s.add(in_city[(d, 'Venice')] == True)
    
    # Constraint: Total days per city
    for c in Cities:
        total = Sum([If(in_city[(d, c)], 1, 0) for d in range(1, 19)])
        s.add(total == required_days[c])
    
    # Constraint: Continuity between consecutive days
    for d in range(1, 18):
        common = Or([And(in_city[(d, c)], in_city[(d+1, c)]) for c in Cities])
        s.add(common)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Print the schedule
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