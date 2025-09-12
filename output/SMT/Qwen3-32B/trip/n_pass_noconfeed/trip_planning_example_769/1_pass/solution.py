import z3

def main():
    solver = z3.Solver()

    # Define cities and their durations
    cities = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
    durations = [5, 4, 4, 2, 2, 4]  # Corresponding to each city in the list

    # Allowed direct flights (bidirectional)
    allowed_transitions = set()
    # Porto and Amsterdam
    allowed_transitions.add((0, 4))
    allowed_transitions.add((4, 0))
    # Munich and Amsterdam
    allowed_transitions.add((5, 4))
    allowed_transitions.add((4, 5))
    # Reykjavik and Amsterdam
    allowed_transitions.add((2, 4))
    allowed_transitions.add((4, 2))
    # Munich and Porto
    allowed_transitions.add((5, 0))
    allowed_transitions.add((0, 5))
    # Prague and Reykjavik
    allowed_transitions.add((1, 2))
    allowed_transitions.add((2, 1))
    # Reykjavik and Munich
    allowed_transitions.add((2, 5))
    allowed_transitions.add((5, 2))
    # Amsterdam and Santorini
    allowed_transitions.add((4, 3))
    allowed_transitions.add((3, 4))
    # Prague and Amsterdam
    allowed_transitions.add((1, 4))
    allowed_transitions.add((4, 1))
    # Prague and Munich
    allowed_transitions.add((1, 5))
    allowed_transitions.add((5, 1))

    # Variables for the order of cities (each is an integer 0-5)
    order = [z3.Int(f'order_{i}') for i in range(6)]

    # Constraints: each city is used exactly once
    for i in range(6):
        solver.add(z3.And(order[i] >= 0, order[i] <= 5))
    solver.add(z3.Distinct(order))

    # Variables for start and end days of each city in the order
    start_days = [z3.Int(f'start_{i}') for i in range(6)]
    end_days = [z3.Int(f'end_{i}') for i in range(6)]

    # First city starts on day 1
    solver.add(start_days[0] == 1)
    solver.add(end_days[0] == start_days[0] + durations[order[0]] - 1)

    # Subsequent cities
    for i in range(1, 6):
        solver.add(start_days[i] == end_days[i-1])
        solver.add(end_days[i] == start_days[i] + durations[order[i]] - 1)

    # The last end day must be 16
    solver.add(end_days[5] == 16)

    # Ensure direct flights between consecutive cities
    for i in range(5):
        prev_city = order[i]
        next_city = order[i+1]
        allowed_pairs = []
        for a, b in allowed_transitions:
            allowed_pairs.append(z3.And(prev_city == a, next_city == b))
        solver.add(z3.Or(allowed_pairs))

    # Constraints for specific events
    for i in range(6):
        # Amsterdam conference on days 14 and 15
        solver.add(z3.Implies(order[i] == 4, z3.And(start_days[i] == 14, end_days[i] == 15)))
        # Munich friend meeting between day 7 and day 10
        solver.add(z3.Implies(order[i] == 5, z3.And(start_days[i] >= 4, start_days[i] <= 10)))
        # Reykjavik wedding between day 4 and day 7
        solver.add(z3.Implies(order[i] == 2, start_days[i] <= 7))

    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract the order of cities
        order_vals = [model.evaluate(order[i]).as_long() for i in range(6)]
        start_vals = [model.evaluate(start_days[i]).as_long() for i in range(6)]
        end_vals = [model.evaluate(end_days[i]).as_long() for i in range(6)]

        # Build the itinerary
        itinerary = []
        for i in range(6):
            city_idx = order_vals[i]
            city_name = cities[city_idx]
            start_day = start_vals[i]
            end_day = end_vals[i]
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})

        # Output as JSON
        import json
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()