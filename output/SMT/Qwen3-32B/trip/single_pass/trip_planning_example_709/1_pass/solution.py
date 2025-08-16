import z3

def main():
    # Define cities and durations
    cities = ['Dubrovnik', 'Helsinki', 'Reykjavik', 'Prague', 'Valencia', 'Porto']
    durations = [4, 4, 4, 3, 5, 3]  # index 0-5

    # Allowed direct flights as pairs (a, b)
    allowed_edges = set([
        (0, 1), (1, 0),  # Dubrovnik-Helsinki, Helsinki-Dubrovnik
        (1, 3), (3, 1),  # Helsinki-Prague, Prague-Helsinki
        (3, 4), (4, 3),  # Prague-Valencia, Valencia-Prague
        (4, 5), (5, 4),  # Valencia-Porto, Porto-Valencia
        (1, 2), (2, 1),  # Helsinki-Reykjavik, Reykjavik-Helsinki
        (2, 3), (3, 2),  # Reykjavik-Prague, Prague-Reykjavik
    ])

    # Create Z3 solver
    s = z3.Solver()

    # Variables for the sequence of cities (each is 0-5)
    seq = [z3.Int(f'seq_{i}') for i in range(6)]

    # Constraints: all cities are distinct
    s.add(z3.Distinct(seq))

    # Each city is between 0 and 5
    for city in seq:
        s.add(z3.And(0 <= city, city <= 5))

    # Consecutive cities must be connected by allowed edges
    for i in range(5):
        current = seq[i]
        next_city = seq[i+1]
        # Create a disjunction of allowed edges
        or_expr = z3.Or([z3.And(current == a, next_city == b) for a, b in allowed_edges])
        s.add(or_expr)

    # Create duration expressions for each position in the sequence
    duration_expr = [0]*6
    for j in range(6):
        city = seq[j]
        duration_expr[j] = z3.If(city == 0, 4,
                    z3.If(city == 1, 4,
                        z3.If(city == 2, 4,
                            z3.If(city == 3, 3,
                                z3.If(city == 4, 5, 3))))

    # Cumulative sum variables
    cum_sum = [z3.Int(f'cum_sum_{i}') for i in range(6)]
    s.add(cum_sum[0] == 0)
    for i in range(1, 6):
        s.add(cum_sum[i] == cum_sum[i-1] + duration_expr[i-1])

    # Constraint for Porto's start day
    for k in range(6):
        s.add(z3.Implies(seq[k] == 5, cum_sum[k] == 15 + k))

    # Check if the model is satisfiable
    if s.check() == z3.sat:
        model = s.model()
        # Extract the sequence
        model_seq = [model.eval(seq[i]).as_long() for i in range(6)]
        # Compute start days
        start_days = [0] * 6
        start_days[0] = 1
        for i in range(1, 6):
            prev_city = model_seq[i-1]
            start_days[i] = start_days[i-1] + durations[prev_city] - 1

        # Now, generate day-to-city mapping
        itinerary = []
        for day in range(1, 19):  # days 1 to 18 inclusive
            for i in range(6):
                start = start_days[i]
                end = start + durations[model_seq[i]] - 1
                if start <= day <= end:
                    city_idx = model_seq[i]
                    city_name = cities[city_idx]
                    itinerary.append({"day": day, "city": city_name})
                    break

        # Output JSON
        import json
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()