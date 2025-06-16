from z3 import *

def main():
    # Cities: Istanbul=0, Rome=1, Seville=2, Naples=3, Santorini=4
    city_names = ['Istanbul', 'Rome', 'Seville', 'Naples', 'Santorini']
    n_cities = 5
    days = 16

    # Flight connections (bidirectional)
    connections = [(0,1), (0,3), (1,2), (1,3), (1,4), (3,4)]
    directed_edges = []
    for (a, b) in connections:
        directed_edges.append((a, b))
        directed_edges.append((b, a))

    # Day variables
    s = [Int(f's_{i}') for i in range(days)]  # Start city each day
    f = [Bool(f'f_{i}') for i in range(days)]  # Flight on day?
    d = [Int(f'd_{i}') for i in range(days)]   # Flight destination

    solver = Solver()

    # Start in Seville on day 1
    solver.add(s[0] == 2)

    # City and flight constraints
    for i in range(days):
        solver.add(s[i] >= 0, s[i] < n_cities)
        solver.add(d[i] >= 0, d[i] < n_cities)
        
        # Flight constraints
        solver.add(Implies(f[i], s[i] != d[i]))
        valid_flight = Or([And(s[i] == a, d[i] == b) for (a, b) in directed_edges])
        solver.add(Implies(f[i], valid_flight))
        
        # Next day's start city
        if i < days-1:
            solver.add(s[i+1] == If(f[i], d[i], s[i]))

    # Event constraints (strict)
    # Istanbul on days 6 and 7 (index 5 and 6)
    solver.add(s[5] == 0)  # Start day 6 in Istanbul
    solver.add(Not(f[5]))   # No flight on day 6
    solver.add(s[6] == 0)  # Start day 7 in Istanbul
    solver.add(Not(f[6]))   # No flight on day 7
    
    # Santorini on day 16 (index 15)
    solver.add(s[15] == 4)  # Start day 16 in Santorini
    solver.add(Not(f[15]))  # No flight on day 16

    # Solve and print itinerary
    if solver.check() == sat:
        model = solver.model()
        print("Day\tStart City\tFlight To")
        for i in range(days):
            s_val = model.evaluate(s[i])
            f_val = model.evaluate(f[i])
            start_city = city_names[s_val.as_long()]
            
            if f_val:
                d_val = model.evaluate(d[i])
                dest_city = city_names[d_val.as_long()]
                print(f"{i+1}\t{start_city}\t\tFly to {dest_city}")
            else:
                print(f"{i+1}\t{start_city}\t\tStay")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()