import z3
import json

def main():
    # Define city names and their corresponding codes
    city_names = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
    durations = {
        'Stuttgart': 2,
        'Bucharest': 2,
        'Geneva': 4,
        'Valencia': 6,
        'Munich': 7
    }

    # Allowed transitions between cities (both directions)
    allowed_transitions = [
        (2, 4), (4, 2),  # Geneva-Munich
        (4, 3), (3, 4),  # Munich-Valencia
        (1, 3), (3, 1),  # Bucharest-Valencia
        (4, 1), (1, 4),  # Munich-Bucharest
        (3, 0), (0, 3),  # Valencia-Stuttgart
        (2, 3), (3, 2)   # Geneva-Valencia
    ]

    # Initialize Z3 solver
    solver = z3.Solver()

    # Variables for itinerary (each city is represented by an integer code)
    itinerary = [z3.Int(f'city_{i}') for i in range(5)]
    for c in itinerary:
        solver.add(z3.And(0 <= c, c <= 4))
    solver.add(z3.Distinct(itinerary))

    # Ensure consecutive transitions are allowed
    for i in range(4):
        current = itinerary[i]
        next_city = itinerary[i + 1]
        allowed = z3.Or([z3.And(current == a, next_city == b) for a, b in allowed_transitions])
        solver.add(allowed)

    # Variables for start days of each city
    S = [z3.Int(f'S_{i}') for i in range(5)]
    solver.add(S[0] == 1)

    # Compute start days based on durations
    for i in range(4):
        duration_i = z3.If(itinerary[i] == 0, 2,
                           z3.If(itinerary[i] == 1, 2,
                                 z3.If(itinerary[i] == 2, 4,
                                       z3.If(itinerary[i] == 3, 6, 7))))
        solver.add(S[i + 1] == S[i] + duration_i - 1)

    # Constraints for Geneva and Munich
    for i in range(5):
        solver.add(z3.Implies(itinerary[i] == 2, S[i] == 1))  # Geneva must start on day 1
        solver.add(z3.Implies(itinerary[i] == 4, S[i] <= 10))  # Munich must start by day 10

    # Check if a solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        order = [model.eval(c).as_long() for c in itinerary]
        start_days = [model.eval(s).as_long() for s in S]

        # Build the result
        result = []
        for i in range(5):
            city_code = order[i]
            city_name = city_names[city_code]
            start_day = start_days[i]
            duration = durations[city_name]
            end_day = start_day + duration - 1
            day_range = f"Day {start_day}-{end_day}"
            result.append({"day_range": day_range, "place": city_name})

        # Output the result in JSON format
        print(json.dumps({"itinerary": result}))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()