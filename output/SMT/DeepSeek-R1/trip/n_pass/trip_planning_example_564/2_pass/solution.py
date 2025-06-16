from z3 import *

def main():
    # Cities: Istanbul=0, Rome=1, Seville=2, Naples=3, Santorini=4
    city_names = ['Istanbul', 'Rome', 'Seville', 'Naples', 'Santorini']
    n_cities = 5
    days = 16

    # Define the directed flight edges (bidirectional connections)
    edges_undirected = [(0, 1), (0, 3), (1, 2), (1, 3), (1, 4), (3, 4)]
    directed_edges = []
    for (a, b) in edges_undirected:
        directed_edges.append((a, b))
        directed_edges.append((b, a))

    # Variables for each day
    s = [Int('s_%d' % i) for i in range(1, days+1)]  # start city of the day
    f = [Bool('f_%d' % i) for i in range(1, days+1)]  # whether we fly on that day
    d = [Int('d_%d' % i) for i in range(1, days+1)]   # destination if flying

    solver = Solver()

    # Constraints for each day
    for i in range(days):
        # City indices must be valid
        solver.add(s[i] >= 0, s[i] < n_cities)
        solver.add(d[i] >= 0, d[i] < n_cities)

        # If flying, must be a valid flight and different cities
        solver.add(Implies(f[i], s[i] != d[i]))
        flight_valid = Or([And(s[i] == a, d[i] == b) for (a, b) in directed_edges])
        solver.add(Implies(f[i], flight_valid))

        # Next day's start city: destination if flew, same if stayed
        if i < days - 1:
            solver.add(If(f[i], s[i+1] == d[i], s[i+1] == s[i]))

    # Total days per city (accounting for flight days)
    total_days = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for i in range(days):
            in_city = Or(s[i] == c, And(f[i], d[i] == c))
            total += If(in_city, 1, 0)
        total_days[c] = total

    solver.add(total_days[0] == 2)  # Istanbul
    solver.add(total_days[1] == 3)  # Rome
    solver.add(total_days[2] == 4)  # Seville
    solver.add(total_days[3] == 7)  # Naples
    solver.add(total_days[4] == 4)  # Santorini

    # Event constraints
    # Must be in Istanbul on day 6 or 7 (or both)
    istanbul_day6 = Or(s[5] == 0, And(f[5], d[5] == 0))
    istanbul_day7 = Or(s[6] == 0, And(f[6], d[6] == 0))
    solver.add(Or(istanbul_day6, istanbul_day7))

    # Must be in Santorini on at least one day from 13 to 16
    santorini_days = []
    for i in range(12, 16):  # Days 13-16 (0-indexed 12-15)
        cond = Or(s[i] == 4, And(f[i], d[i] == 4))
        santorini_days.append(cond)
    solver.add(Or(santorini_days))

    # Additional constraint: Do not fly on the last day to remain in Santorini
    solver.add(Not(f[15]))  # Day 16 (index 15) has no flight

    # Solve and print the itinerary
    if solver.check() == sat:
        model = solver.model()
        print("Day\tStart City\tFlight To")
        for i in range(days):
            s_val = model.evaluate(s[i])
            f_val = model.evaluate(f[i])
            d_val = model.evaluate(d[i])
            start_city_name = city_names[s_val.as_long()]
            if f_val:
                flight_dest_name = city_names[d_val.as_long()]
                print(f"{i+1}\t{start_city_name}\t\tFly to {flight_dest_name}")
            else:
                print(f"{i+1}\t{start_city_name}\t\tStay")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()