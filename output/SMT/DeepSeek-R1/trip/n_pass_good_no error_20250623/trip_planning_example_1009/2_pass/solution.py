import z3
import json

def main():
    # Mapping of city names to indices
    city_names = ["Riga", "Manchester", "Bucharest", "Florence", "Vienna", "Istanbul", "Reykjavik", "Stuttgart"]
    days_required = [4, 5, 4, 4, 2, 2, 4, 5]  # Corresponding to the cities above

    # Allowed directed flight edges: (from_city_index, to_city_index)
    allowed_edges = [
        (0, 4), (4, 0), (1, 4), (4, 1), (1, 0), (0, 1),
        (5, 4), (4, 5), (4, 3), (3, 4), (4, 7), (7, 4),
        (0, 2), (2, 0), (5, 0), (0, 5), (7, 5), (5, 7),
        (6, 7),  # Only one-way from Reykjavik to Stuttgart
        (5, 2), (2, 5), (1, 5), (5, 1), (1, 2), (2, 1), (7, 1), (1, 7)
    ]

    # Create Z3 variables
    solver = z3.Solver()
    pos = [z3.Int(f'pos_{i}') for i in range(8)]  # City index at each position
    s = [z3.Int(f's_{i}') for i in range(8)]      # Start day for each position
    e = [z3.Int(f'e_{i}') for i in range(8)]      # End day for each position

    # Constraints for city permutation: each city index between 0 and 7, all distinct
    for i in range(8):
        solver.add(pos[i] >= 0, pos[i] < 8)
    solver.add(z3.Distinct(pos))

    # Start and end day constraints
    solver.add(s[0] == 1)  # Start on day 1
    for i in range(7):
        solver.add(s[i+1] == e[i])  # Next city starts on the end day of the current city (flight day)
    for i in range(8):
        # Build the expression for required days based on the city at position i
        req_days = z3.If(pos[i] == 0, days_required[0],
                  z3.If(pos[i] == 1, days_required[1],
                  z3.If(pos[i] == 2, days_required[2],
                  z3.If(pos[i] == 3, days_required[3],
                  z3.If(pos[i] == 4, days_required[4],
                  z3.If(pos[i] == 5, days_required[5],
                  z3.If(pos[i] == 6, days_required[6],
                  z3.If(pos[i] == 7, days_required[7], 0))))))))
        solver.add(e[i] == s[i] + req_days - 1)

    # Flight constraints: consecutive cities must have a direct flight
    for i in range(7):
        edge_conds = []
        for edge in allowed_edges:
            from_city, to_city = edge
            edge_conds.append(z3.And(pos[i] == from_city, pos[i+1] == to_city))
        solver.add(z3.Or(edge_conds))

    # Event constraints: entire event period must be within the stay
    for i in range(8):
        # Istanbul (index 5) must cover days 12 and 13
        solver.add(z3.If(pos[i] == 5, z3.And(s[i] <= 12, e[i] >= 13), True))
        # Bucharest (index 2) must cover days 16 to 19
        solver.add(z3.If(pos[i] == 2, z3.And(s[i] <= 16, e[i] >= 19), True))

    # Check and get the model
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary_list = []

        # Evaluate the model to get concrete values
        pos_vals = [model.eval(pos[i]).as_long() for i in range(8)]
        s_vals = [model.eval(s[i]).as_long() for i in range(8)]
        e_vals = [model.eval(e[i]).as_long() for i in range(8)]

        # Build the itinerary
        for i in range(8):
            city_idx = pos_vals[i]
            city_name = city_names[city_idx]
            start = s_vals[i]
            end = e_vals[i]
            # Add the entire stay block
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range_str, "place": city_name})
            
            # If not the last city, add flight records
            if i < 7:
                # Departure from current city on the end day
                itinerary_list.append({"day_range": f"Day {end}", "place": city_name})
                # Arrival in next city on the same day
                next_city_idx = pos_vals[i+1]
                next_city_name = city_names[next_city_idx]
                itinerary_list.append({"day_range": f"Day {end}", "place": next_city_name})
        
        # Output as JSON
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()