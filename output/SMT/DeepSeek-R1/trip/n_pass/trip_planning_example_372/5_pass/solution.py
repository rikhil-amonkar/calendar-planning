from z3 import *

def main():
    n_days = 13
    cities = ['Madrid', 'Seville', 'Porto', 'Stuttgart']
    city_to_int = {c: idx for idx, c in enumerate(cities)}
    direct_flights = [('Madrid', 'Seville'), ('Madrid', 'Porto'), ('Seville', 'Porto'), ('Porto', 'Stuttgart')]
    allowed_pairs = set()
    for a, b in direct_flights:
        a_idx = city_to_int[a]
        b_idx = city_to_int[b]
        allowed_pairs.add((a_idx, b_idx))
        allowed_pairs.add((b_idx, a_idx))
    
    s = [Int(f's_{i}') for i in range(n_days)]
    d = [Int(f'd_{i}') for i in range(n_days)]
    travel = [Bool(f'travel_{i}') for i in range(n_days)]
    
    solver = Solver()
    
    for i in range(n_days):
        solver.add(s[i] >= 0, s[i] < 4)
        solver.add(d[i] >= 0, d[i] < 4)
    
    # Constraints for Madrid (days 1-4)
    solver.add(s[0] == city_to_int['Madrid'])
    solver.add(s[1] == city_to_int['Madrid'])
    solver.add(s[2] == city_to_int['Madrid'])
    solver.add(s[3] == city_to_int['Madrid'])
    
    # No travel on first 3 days
    solver.add(travel[0] == False)
    solver.add(travel[1] == False)
    solver.add(travel[2] == False)
    
    # Stuttgart on day 7 (start) and day 13
    solver.add(s[6] == city_to_int['Stuttgart'])  # Start of day 7
    solver.add(s[12] == city_to_int['Stuttgart']) # Start of day 13
    
    # No travel on day 13
    solver.add(travel[12] == False)
    solver.add(d[12] == city_to_int['Stuttgart'])
    
    # Continuity between days
    for i in range(1, n_days):
        solver.add(s[i] == d[i-1])
    
    # Travel constraints
    for i in range(n_days):
        solver.add(If(travel[i], d[i] != s[i], d[i] == s[i]))
        if i != 12:  # Skip day 13 (already handled)
            solver.add(Implies(travel[i], Or([And(s[i] == a, d[i] == b) for (a, b) in allowed_pairs])))
    
    # Total travel days = 3
    total_travel = Sum([If(travel[i], 1, 0) for i in range(n_days)])
    solver.add(total_travel == 3)
    
    # City day counts
    counts = [0]*4
    for c in range(4):
        total = 0
        for i in range(n_days):
            total += If(s[i] == c, 1, 0)
            total += If(And(travel[i], d[i] == c), 1, 0)
        counts[c] = total
    
    solver.add(counts[city_to_int['Madrid']] == 4)
    solver.add(counts[city_to_int['Seville']] == 2)
    solver.add(counts[city_to_int['Porto']] == 3)
    solver.add(counts[city_to_int['Stuttgart']] == 7)
    
    if solver.check() == sat:
        model = solver.model()
        start_vals = [model.evaluate(s[i]).as_long() for i in range(n_days)]
        travel_vals = [is_true(model.evaluate(travel[i])) for i in range(n_days)]
        dest_vals = [model.evaluate(d[i]).as_long() for i in range(n_days)]
        
        output = []
        for i in range(n_days):
            if travel_vals[i]:
                output.append([cities[start_vals[i]], cities[dest_vals[i]]])
            else:
                output.append([cities[start_vals[i]]])
        
        for day, cities_list in enumerate(output, 1):
            print(f"Day {day}: {cities_list}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()