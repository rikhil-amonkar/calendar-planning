from z3 import *

def main():
    # City indices and their required stay durations
    city_names = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    L_arr = [4, 2, 3, 2, 3, 4, 3]  # days per city

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
    S = [Int('S_%d' % i) for i in range(7)]   # start days for each city
    E = [Int('E_%d' % i) for i in range(7)]   # end days for each city

    s = Solver()

    # First city must be Vienna (index 0)
    s.add(c[0] == 0)
    # Ensure distinct cities in permutation
    for i in range(1, 7):
        s.add(c[i] >= 1, c[i] <= 6)
    s.add(Distinct(c))

    # Helper function to get stay duration for a city variable
    def get_duration(city_var):
        # Create nested If expressions to map city index to duration
        expr = If(city_var == 6, L_arr[6], 0)  # Oslo
        expr = If(city_var == 5, L_arr[5], expr)  # Vilnius
        expr = If(city_var == 4, L_arr[4], expr)  # Lisbon
        expr = If(city_var == 3, L_arr[3], expr)  # Riga
        expr = If(city_var == 2, L_arr[2], expr)  # Rome
        expr = If(city_var == 1, L_arr[1], expr)  # Milan
        expr = If(city_var == 0, L_arr[0], expr)  # Vienna
        return expr

    # Start and end days for the first city (Vienna)
    s.add(S[0] == 1)
    s.add(E[0] == S[0] + get_duration(c[0]) - 1)

    # Start and end days for subsequent cities
    for i in range(1, 7):
        # End day of previous city is the start day of the next city
        s.add(S[i] == E[i-1] + 1)
        s.add(E[i] == S[i] + get_duration(c[i]) - 1)

    # Constraints for Lisbon (index 4) and Oslo (index 6) start days
    for i in range(7):
        s.add(Implies(c[i] == 4, S[i] == 11))  # Lisbon must start on day 11
        s.add(Implies(c[i] == 6, S[i] == 13))  # Oslo must start on day 13

    # Flight constraints between consecutive cities
    for i in range(6):
        options = []
        for (u, v) in directed_edges:
            options.append(And(c[i] == u, c[i+1] == v))
        s.add(Or(options))

    # Total days must be 15
    s.add(E[6] == 15)

    # Solve and generate itinerary if solution exists
    if s.check() == sat:
        model = s.model()
        perm = [model.eval(c[i]).as_long() for i in range(7)]
        start_days = [model.eval(S[i]).as_long() for i in range(7)]
        end_days = [model.eval(E[i]).as_long() for i in range(7)]
        
        # Create a list for each day indicating the city
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