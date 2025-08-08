from z3 import *

def main():
    # City indices: 0:Vienna, 1:Milan, 2:Rome, 3:Riga, 4:Lisbon, 5:Vilnius, 6:Oslo
    city_names = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    L_arr = [4, 2, 3, 2, 3, 4, 3]  # required days per city
    L_minus = [l - 1 for l in L_arr]  # days minus one for start day calculation

    # Build directed flight graph
    directed_edges = set()
    bidirectional_pairs = [
        (3, 6), (2, 6), (0, 1), (0, 5), (0, 4), (3, 1), (4, 6), (2, 4),
        (0, 3), (0, 2), (1, 6), (0, 6), (5, 6), (5, 1), (3, 4), (1, 4)
    ]
    for u, v in bidirectional_pairs:
        directed_edges.add((u, v))
        directed_edges.add((v, u))
    oneway_edges = [(2, 3), (3, 5)]  # Rome to Riga, Riga to Vilnius
    for u, v in oneway_edges:
        directed_edges.add((u, v))

    # Z3 variables: c[0..6] for the permutation of cities
    c = [Int('c_%d' % i) for i in range(7)]
    S_expr = [Int('S_%d' % i) for i in range(7)]  # start days for each city in the sequence

    s = Solver()

    # Constraint: first city is Vienna (index 0)
    s.add(c[0] == 0)

    # Constraints: c[1..6] are distinct and between 1 and 6
    for i in range(1, 7):
        s.add(c[i] >= 1, c[i] <= 6)
    s.add(Distinct(c))

    # Helper function to get L_minus for a city index
    def get_L_minus(city_var):
        return If(city_var == 0, L_minus[0],
                If(city_var == 1, L_minus[1],
                If(city_var == 2, L_minus[2],
                If(city_var == 3, L_minus[3],
                If(city_var == 4, L_minus[4],
                If(city_var == 5, L_minus[5], L_minus[6])))))

    # Constraints for start days: S[0]=1, and S[k] = S[k-1] + L_minus(c[k-1])
    s.add(S_expr[0] == 1)
    for k in range(1, 7):
        s.add(S_expr[k] == S_expr[k-1] + get_L_minus(c[k-1]))

    # Constraints for Lisbon (city4) and Oslo (city6) start days
    for k in range(7):
        s.add(Implies(c[k] == 4, And(S_expr[k] >= 9, S_expr[k] <= 13)))  # Lisbon
        s.add(Implies(c[k] == 6, And(S_expr[k] >= 11, S_expr[k] <= 13)))  # Oslo

    # Flight constraints between consecutive cities
    for i in range(6):
        options = []
        for (u, v) in directed_edges:
            options.append(And(c[i] == u, c[i+1] == v))
        s.add(Or(options))

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        # Extract the permutation and start days
        perm = [model.eval(c[i]).as_long() for i in range(7)]
        start_days = [model.eval(S_expr[i]).as_long() for i in range(7)]
        end_days = [start_days[i] + L_arr[perm[i]] - 1 for i in range(7)]
        
        # Build itinerary for each day (1 to 15)
        itinerary = []
        for day in range(1, 16):
            cities_today = []
            for idx in range(7):
                if day >= start_days[idx] and day <= end_days[idx]:
                    cities_today.append(city_names[perm[idx]])
            itinerary.append({"day": day, "city": cities_today})
        
        # Output as JSON-formatted dictionary
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()