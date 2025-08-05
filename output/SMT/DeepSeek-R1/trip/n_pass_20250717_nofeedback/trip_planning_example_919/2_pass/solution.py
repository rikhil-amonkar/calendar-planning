from z3 import *

def main():
    # City indices and their required stay durations
    city_names = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    L_arr = [4, 2, 3, 2, 3, 4, 3]  # days per city
    L_minus = [l - 1 for l in L_arr]  # days minus one for flight day adjustment

    # Directed flight connections
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

    # Z3 variables for city permutation and start days
    c = [Int('c_%d' % i) for i in range(7)]  # city order
    S_expr = [Int('S_%d' % i) for i in range(7)]  # start days for each city

    s = Solver()

    # First city must be Vienna (index 0)
    s.add(c[0] == 0)
    # Ensure distinct cities in permutation
    for i in range(1, 7):
        s.add(c[i] >= 1, c[i] <= 6)
    s.add(Distinct(c))

    # Helper function to get adjusted stay duration for start day calculation
    def get_L_minus(city_var):
        expr = L_minus[6]  # default for Oslo (index 6)
        for i in range(5, -1, -1):  # build nested If conditions from 5 down to 0
            expr = If(city_var == i, L_minus[i], expr)
        return expr

    # Compute start days: S[0]=1, S[k] = S[k-1] + L_minus(c[k-1])
    s.add(S_expr[0] == 1)
    for k in range(1, 7):
        s.add(S_expr[k] == S_expr[k-1] + get_L_minus(c[k-1]))

    # Constraints for Lisbon (index 4) and Oslo (index 6) start days
    for k in range(7):
        s.add(Implies(c[k] == 4, S_expr[k] == 11))  # Lisbon must start on day 11
        s.add(Implies(c[k] == 6, S_expr[k] == 13))  # Oslo must start on day 13

    # Flight constraints between consecutive cities
    for i in range(6):
        options = []
        for (u, v) in directed_edges:
            options.append(And(c[i] == u, c[i+1] == v))
        s.add(Or(options))

    # Solve and generate itinerary if solution exists
    if s.check() == sat:
        model = s.model()
        perm = [model.eval(c[i]).as_long() for i in range(7)]
        start_days = [model.eval(S_expr[i]).as_long() for i in range(7)]
        end_days = [start_days[i] + L_arr[perm[i]] - 1 for i in range(7)]
        
        itinerary = []
        for day in range(1, 16):
            cities_today = []
            for idx in range(7):
                if start_days[idx] <= day <= end_days[idx]:
                    cities_today.append(city_names[perm[idx]])
            itinerary.append({"day": day, "city": cities_today})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()