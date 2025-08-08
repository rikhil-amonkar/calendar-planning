def main():
    # Import Z3 inside the function to avoid initialization conflicts
    from z3 import Int, Bool, Solver, If, And, Or, Sum, sat
    
    city_names = {0: 'Madrid', 1: 'Dublin', 2: 'Tallinn'}
    solver = Solver()
    
    # City variables for days 1-7
    s = [Int(f's_{i}') for i in range(1, 8)]
    # Travel flags for days 1-6
    t = [Bool(f't_{i}') for i in range(1, 7)]
    
    # City domain constraints
    for i in range(7):
        solver.add(s[i] >= 0, s[i] <= 2)
    
    # Tallinn workshop on days 6-7
    solver.add(s[6] == 2)  # s[6] is day 7
    
    # Travel constraints
    for i in range(6):
        direct_flight = Or(
            And(s[i] == 0, s[i+1] == 1),
            And(s[i] == 1, s[i+1] == 0),
            And(s[i] == 1, s[i+1] == 2),
            And(s[i] == 2, s[i+1] == 1)
        )
        solver.add(If(t[i], direct_flight, s[i] == s[i+1]))
    
    # City day counters
    madrid_days = []
    dublin_days = []
    tallinn_days = []
    
    # Count starting cities
    for i in range(7):
        madrid_days.append(If(s[i] == 0, 1, 0))
        dublin_days.append(If(s[i] == 1, 1, 0))
        tallinn_days.append(If(s[i] == 2, 1, 0))
        
        # Count arrival cities for travel days
        if i < 6:
            madrid_days.append(If(And(t[i], s[i+1] == 0), 1, 0))
            dublin_days.append(If(And(t[i], s[i+1] == 1), 1, 0))
            tallinn_days.append(If(And(t[i], s[i+1] == 2), 1, 0))
    
    # Add city total constraints
    solver.add(Sum(madrid_days) == 4)
    solver.add(Sum(dublin_days) == 3)
    solver.add(Sum(tallinn_days) == 2)
    
    # Exactly 2 travel days
    solver.add(Sum([If(t_i, 1, 0) for t_i in t]) == 2)
    
    # Solve and output
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        s_vals = [m.evaluate(s_i).as_long() for s_i in s]
        t_vals = [m.evaluate(t_i) for t_i in t]
        
        for day in range(1, 8):
            idx = day - 1
            itinerary.append({'day': day, 'city': city_names[s_vals[idx]]})
            if day < 7 and t_vals[idx]:
                itinerary.append({'day': day, 'city': city_names[s_vals[idx+1]]})
        
        print({'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == '__main__':
    main()