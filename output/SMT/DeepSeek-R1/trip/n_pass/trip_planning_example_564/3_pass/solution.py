from z3 import *

def main():
    # Cities: Istanbul=0, Rome=1, Seville=2, Naples=3, Santorini=4
    city_names = ['Istanbul', 'Rome', 'Seville', 'Naples', 'Santorini']
    n_cities = 5
    days = 16

    # Define directed flights (bidirectional connections)
    edges_undirected = [(0, 1), (0, 3), (1, 2), (1, 3), (1, 4), (3, 4)]
    directed_edges = []
    for (a, b) in edges_undirected:
        directed_edges.append((a, b))
        directed_edges.append((b, a))

    # Variables for each day
    s = [Int('s_%d' % i) for i in range(1, days+1)]  # start city
    f = [Bool('f_%d' % i) for i in range(1, days+1)]  # flight occurrence
    d = [Int('d_%d' % i) for i in range(1, days+1)]   # flight destination

    solver = Solver()

    # City and flight constraints
    for i in range(days):
        solver.add(s[i] >= 0, s[i] < n_cities)
        solver.add(d[i] >= 0, d[i] < n_cities)
        solver.add(Implies(f[i], s[i] != d[i]))
        valid_flight = Or([And(s[i] == a, d[i] == b) for (a, b) in directed_edges])
        solver.add(Implies(f[i], valid_flight))
        if i < days - 1:
            solver.add(If(f[i], s[i+1] == d[i], s[i+1] == s[i]))

    # Total days per city (accounting for flight days)
    totals = [0]*n_cities
    for c in range(n_cities):
        total = 0
        for i in range(days):
            in_city = Or(s[i] == c, And(f[i], d[i] == c))
            total += If(in_city, 1, 0)
        totals[c] = total

    solver.add(totals[0] == 2)  # Istanbul
    solver.add(totals[1] == 3)  # Rome
    solver.add(totals[2] == 4)  # Seville
    solver.add(totals[3] == 7)  # Naples
    solver.add(totals[4] == 4)  # Santorini

    # Event constraints
    # Must be in Istanbul on both day 6 and 7
    for i in [5, 6]:  # Days 6 and 7 (0-indexed)
        in_istanbul = Or(s[i] == 0, And(f[i], d[i] == 0))
        solver.add(in_istanbul)
    
    # Must be in Santorini on day 16
    in_santorini_day16 = Or(s[15] == 4, And(f[15], d[15] == 4))
    solver.add(in_santorini_day16)

    # Solve and print itinerary
    if solver.check() == sat:
        model = solver.model()
        print("Day\tStart City\tFlight To")
        for i in range(days):
            s_val = model.evaluate(s[i])
            f_val = model.evaluate(f[i])
            d_val = model.evaluate(d[i])
            start_city = city_names[s_val.as_long()]
            if f_val:
                dest = city_names[d_val.as_long()]
                print(f"{i+1}\t{start_city}\t\tFly to {dest}")
            else:
                print(f"{i+1}\t{start_city}\t\tStay")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()