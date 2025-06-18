from z3 import *

def main():
    # Define the list of 8 middle cities (positions 1 to 8)
    all_cities = ["Istanbul", "Vienna", "Riga", "Madrid", "Vilnius", "Venice", "Munich", "Reykjavik"]
    # Global list of all 10 cities with their indices
    global_cities = ["Geneva", "Istanbul", "Vienna", "Riga", "Brussels", "Madrid", "Vilnius", "Venice", "Munich", "Reykjavik"]
    name_to_index = {name: idx for idx, name in enumerate(global_cities)}
    # Mapping from the 8-city list to global indices
    global_indices_for_middle = [name_to_index[city] for city in all_cities]  # [1,2,3,5,6,7,8,9]

    # Define the direct_edges set (as tuples of city names)
    direct_edges = [
        ("Munich", "Vienna"),
        ("Istanbul", "Brussels"),
        ("Vienna", "Vilnius"),
        ("Madrid", "Munich"),
        ("Venice", "Brussels"),
        ("Riga", "Brussels"),
        ("Geneva", "Istanbul"),
        ("Munich", "Reykjavik"),
        ("Vienna", "Istanbul"),
        ("Riga", "Istanbul"),
        ("Reykjavik", "Vienna"),
        ("Venice", "Munich"),
        ("Madrid", "Venice"),
        ("Vilnius", "Istanbul"),
        ("Venice", "Vienna"),
        ("Venice", "Istanbul"),
        ("Reykjavik", "Madrid"),
        ("Riga", "Munich"),
        ("Munich", "Istanbul"),
        ("Reykjavik", "Brussels"),
        ("Vilnius", "Brussels"),
        ("Vilnius", "Munich"),
        ("Madrid", "Vienna"),
        ("Vienna", "Riga"),
        ("Geneva", "Vienna"),
        ("Madrid", "Brussels"),
        ("Vienna", "Brussels"),
        ("Geneva", "Brussels"),
        ("Geneva", "Madrid"),
        ("Munich", "Brussels"),
        ("Madrid", "Istanbul"),
        ("Geneva", "Munich"),
        ("Riga", "Vilnius")
    ]
    # Build a set of directed edges (both directions) as global index pairs
    allowed_directed_edges = set()
    for (a, b) in direct_edges:
        u = name_to_index[a]
        v = name_to_index[b]
        allowed_directed_edges.add((u, v))
        allowed_directed_edges.add((v, u))

    # Create Z3 variables
    c = [Int('c%d' % i) for i in range(8)]  # for the 8 middle positions (each c[i] in [0,7])
    f_vars = [Int('f%d' % i) for i in range(1,8)]  # f1 to f7
    F = [4] + f_vars + [26]  # F[0]=4, F[1]=f1, ... F[7]=f7, F[8]=26

    s = Solver()

    # Constraint 1: c0..c7 are distinct and in [0,7]
    s.add(Distinct(c))
    for i in range(8):
        s.add(c[i] >= 0, c[i] < 8)

    # Constraint 2: Flight days are strictly increasing integers
    for i in range(8):  # from F[0] to F[8], but F[0] and F[8] fixed
        s.add(F[i+1] > F[i])
        s.add(F[i+1] >= F[i] + 1)  # at least one day apart

    # Constraint 3: For cities that are Venice or Vilnius, fix the flight days
    for i in range(1, 9):  # i from 1 to 8 (position in the sequence for middle cities)
        # The city at position i is: all_cities[ c[i-1] ]
        # We represent the condition by the index in all_cities
        # If c[i-1] == index of Venice in all_cities? Venice is at index 5 in all_cities? 
        # But note: all_cities[5] is "Venice", all_cities[4] is "Vilnius"
        # So: 
        #   If c[i-1] == 5, then it's Venice -> then F[i-1] = 7 and F[i] = 11
        #   If c[i-1] == 4, then it's Vilnius -> then F[i-1] = 20 and F[i] = 23
        s.add(If(c[i-1] == 5, And(F[i-1] == 7, F[i] == 11), True))
        s.add(If(c[i-1] == 4, And(F[i-1] == 20, F[i] == 23), True))

    # Constraint 4: For non-Venice, non-Vilnius cities, the lengths must be 2,2,4,4,4,5
    non_fixed_lengths = []
    for i in range(1,9):  # for position i
        length_i = F[i] - F[i-1] + 1
        # The city at position i is all_cities[ c[i-1] ]
        # If it is Venice (index5 in all_cities) or Vilnius (index4 in all_cities), skip
        condition = Or(c[i-1] == 5, c[i-1] == 4)
        non_fixed_lengths.append(If(condition, -1, length_i))   # use -1 as dummy for fixed ones, then we filter

    # Now, collect the actual non-fixed lengths (ignore -1)
    actual_lengths = []
    for x in non_fixed_lengths:
        actual_lengths.append(If(x == -1, 0, x))   # we will count non-dummy

    # Count the occurrences of 2, 4, 5 in the actual non-fixed lengths
    count2 = Sum([If(And(x != -1, x == 2), 1, 0) for x in non_fixed_lengths])
    count4 = Sum([If(And(x != -1, x == 4), 1, 0) for x in non_fixed_lengths])
    count5 = Sum([If(And(x != -1, x == 5), 1, 0) for x in non_fixed_lengths])
    s.add(count2 == 2)
    s.add(count4 == 3)
    s.add(count5 == 1)

    # Constraint 5: Direct flights between consecutive cities
    # Build the sequence of global indices for the 10 cities
    s0 = 0  # Geneva
    s1 = global_indices_for_middle[c[0]]
    s2 = global_indices_for_middle[c[1]]
    s3 = global_indices_for_middle[c[2]]
    s4 = global_indices_for_middle[c[3]]
    s5 = global_indices_for_middle[c[4]]
    s6 = global_indices_for_middle[c[5]]
    s7 = global_indices_for_middle[c[6]]
    s8 = global_indices_for_middle[c[7]]
    s9 = 4  # Brussels

    seq_global = [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]

    # For each consecutive pair in the sequence
    for i in range(9):  # from 0 to 8
        a = seq_global[i]
        b = seq_global[i+1]
        # The edge (a,b) must be in allowed_directed_edges
        cond = False
        for (u, v) in allowed_directed_edges:
            cond = Or(cond, And(a == u, b == v))
        s.add(cond)

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        # Get the values for c0..c7
        c_vals = [m.evaluate(c[i]) for i in range(8)]
        # Get the flight days f1 to f7
        f_vals = [m.evaluate(f_vars[i]) for i in range(7)]
        F_vals = [4] + [int(f_vals[i].as_long()) for i in range(7)] + [26]

        # Build the sequence of cities
        seq_cities = ["Geneva"]  # city0
        for i in range(8):
            idx = int(c_vals[i].as_long())
            seq_cities.append(all_cities[idx])
        seq_cities.append("Brussels")  # city9

        # Build itinerary
        itinerary = []
        # For each city in the sequence
        for i in range(10):
            city_name = seq_cities[i]
            start_day = F_vals[i-1] if i > 0 else 1
            end_day = F_vals[i] if i < 9 else 27
            # The continuous block
            if start_day == end_day:
                block_str = "Day %d" % start_day
            else:
                block_str = "Day %d-%d" % (start_day, end_day)
            itinerary.append({"day_range": block_str, "place": city_name})
            # If not the last city, add flight day records
            if i < 9:
                # Departure from current city on flight day (end_day)
                itinerary.append({"day_range": "Day %d" % end_day, "place": city_name})
                # Arrival in next city on flight day (end_day)
                next_city = seq_cities[i+1]
                itinerary.append({"day_range": "Day %d" % end_day, "place": next_city})

        # Output as JSON
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()