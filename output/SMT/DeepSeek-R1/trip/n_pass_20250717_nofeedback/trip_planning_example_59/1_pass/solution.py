import z3

def main():
    # Create solver
    solver = z3.Solver()
    
    # Create a 16x3 grid of boolean variables: days 0 to 15, cities: 0=Bucharest, 1=Lyon, 2=Porto
    b = [[z3.Bool(f"day{i}_city{j}") for j in range(3)] for i in range(16)]
    
    # For each day, add constraints: at least one city, at most two, and only valid combinations
    for i in range(16):
        # At least one city
        solver.add(z3.Or(b[i][0], b[i][1], b[i][2]))
        
        # Not all three at the same time
        solver.add(z3.Not(z3.And(b[i][0], b[i][1], b[i][2])))
        
        # Not Bucharest and Porto without Lyon (since no direct flight)
        solver.add(z3.Implies(z3.And(b[i][0], b[i][2]), b[i][1]))
        
        # But also, we don't want Bucharest and Porto together at all? 
        # Actually, if they are together, then Lyon must be there, but then we have three which is forbidden.
        # So the above implication and the not all three already prevent (Bucharest and Porto) without Lyon? 
        # But we can also explicitly prevent (Bucharest and Porto) without Lyon? 
        # The above implication does that: if Bucharest and Porto are true, then Lyon must be true -> but then we have all three which is forbidden by the previous constraint.
        # So we are safe.
    
    # Total days in each city
    total_b = z3.Sum([z3.If(b[i][0], 1, 0) for i in range(16)])
    total_l = z3.Sum([z3.If(b[i][1], 1, 0) for i in range(16)])
    total_p = z3.Sum([z3.If(b[i][2], 1, 0) for i in range(16)])
    solver.add(total_b == 7, total_l == 7, total_p == 4)
    
    # Wedding constraint: at least one day in [1,7] (days 0 to 6) in Bucharest
    solver.add(z3.Or([b[i][0] for i in range(7)]))
    
    # Connectivity: consecutive days share at least one city
    for i in range(15):
        solver.add(z3.Or(
            z3.And(b[i][0], b[i+1][0]),
            z3.And(b[i][1], b[i+1][1]),
            z3.And(b[i][2], b[i+1][2])
        ))
    
    # Start constraint: exactly one city on day 0
    solver.add(z3.Or(
        z3.And(b[0][0], z3.Not(b[0][1]), z3.Not(b[0][2])),
        z3.And(z3.Not(b[0][0]), b[0][1], z3.Not(b[0][2])),
        z3.And(z3.Not(b[0][0]), z3.Not(b[0][1]), b[0][2])
    ))
    
    # Check and get the model
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        city_names = ["Bucharest", "Lyon", "Porto"]
        for i in range(16):
            day = i + 1
            # Evaluate the booleans for this day
            vals = []
            for j in range(3):
                val = model.evaluate(b[i][j])
                if z3.is_true(val):
                    vals.append(city_names[j])
            if len(vals) == 1:
                city_str = vals[0]
            elif len(vals) == 2:
                city_str = " and ".join(vals)
            else:
                # Should not happen by constraints
                city_str = "ERROR"
            itinerary.append({"day": day, "city": city_str})
        
        # Output as JSON
        import json
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()