import z3

def main():
    # City indices
    cities = ["Venice", "Barcelona", "Copenhagen", "Lyon", "Reykjavik", "Dubrovnik", "Athens", "Tallinn", "Munich"]
    city_to_index = {name: idx for idx, name in enumerate(cities)}
    
    # Stay lengths for each city
    lengths_dict = {
        city_to_index["Venice"]: 4,
        city_to_index["Barcelona"]: 3,
        city_to_index["Copenhagen"]: 4,
        city_to_index["Lyon"]: 4,
        city_to_index["Reykjavik"]: 4,
        city_to_index["Dubrovnik"]: 5,
        city_to_index["Athens"]: 2,
        city_to_index["Tallinn"]: 5,
        city_to_index["Munich"]: 3
    }
    
    L_minus = [lengths_dict[i] - 1 for i in range(9)]
    
    # Direct flight list (as integer pairs)
    edges_list = [
        (2,6), (2,5), (8,7), (2,8), (0,8), (4,6), (6,5), (0,6), (3,1), 
        (2,4), (4,8), (6,8), (3,8), (1,4), (0,2), (1,5), (3,0), (5,8),
        (1,6), (2,1), (0,1), (1,8), (1,7), (2,7)
    ]
    
    # Create Z3 variables for the sequence of cities
    seq = [z3.Int(f'seq_{i}') for i in range(9)]
    solver = z3.Solver()
    
    # Domain constraint: each seq[i] in [0,8]
    domain_c = [z3.And(seq[i] >= 0, seq[i] < 9) for i in range(9)]
    solver.add(domain_c)
    
    # Distinct constraint
    solver.add(z3.Distinct(seq))
    
    # Base expressions for cumulative (length-1) sums
    base_expr = [0] * 9
    base_expr[0] = 0
    for i in range(1, 9):
        expr_i = None
        for j in range(9):
            cond = (seq[i-1] == j)
            if j == 0:
                expr_i = z3.If(cond, L_minus[j], 0)
            else:
                expr_i = z3.If(cond, L_minus[j], expr_i)
        base_expr[i] = base_expr[i-1] + expr_i
    
    # Event constraints: Barcelona, Copenhagen, Dubrovnik
    barcelona_cond = []
    for k in range(9):
        start_day = 1 + base_expr[k]
        cond = z3.If(seq[k] == city_to_index["Barcelona"], 
                     z3.And(start_day >= 8, start_day <= 12),
                     True)
        barcelona_cond.append(cond)
    solver.add(barcelona_cond)
    
    copenhagen_cond = []
    for k in range(9):
        start_day = 1 + base_expr[k]
        cond = z3.If(seq[k] == city_to_index["Copenhagen"], 
                     z3.And(start_day >= 4, start_day <= 10),
                     True)
        copenhagen_cond.append(cond)
    solver.add(copenhagen_cond)
    
    dubrovnik_cond = []
    for k in range(9):
        start_day = 1 + base_expr[k]
        cond = z3.If(seq[k] == city_to_index["Dubrovnik"], 
                     z3.And(start_day >= 12, start_day <= 20),
                     True)
        dubrovnik_cond.append(cond)
    solver.add(dubrovnik_cond)
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(8):
        conds = []
        for (a, b) in edges_list:
            conds.append(z3.Or(
                z3.And(seq[i] == a, seq[i+1] == b),
                z3.And(seq[i] == b, seq[i+1] == a)
            ))
        solver.add(z3.Or(conds))
    
    # Solve
    if solver.check() == z3.sat:
        model = solver.model()
        model_seq = [model[seq[i]].as_long() for i in range(9)]
        
        # Compute base_val, start days (S), and end days (E)
        base_val = [0] * 9
        for i in range(1, 9):
            prev_city = model_seq[i-1]
            base_val[i] = base_val[i-1] + (lengths_dict[prev_city] - 1)
        
        S_val = [1 + base_val[i] for i in range(9)]
        E_val = [S_val[i] + lengths_dict[model_seq[i]] - 1 for i in range(9)]
        
        # Build itinerary for days 1 to 26
        itinerary = []
        for day in range(1, 27):
            places = []
            for k in range(9):
                if day >= S_val[k] and day <= E_val[k]:
                    places.append(cities[model_seq[k]])
            itinerary.append({"day": day, "place": places})
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()