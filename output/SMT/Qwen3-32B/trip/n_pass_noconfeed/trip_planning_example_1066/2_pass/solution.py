from z3 import *

def main():
    # Define cities and durations
    cities_names = ["Brussels", "Bucharest", "Stuttgart", "Mykonos", "Madrid", "Helsinki", "Split", "London"]
    durations = [4, 3, 4, 2, 2, 5, 3, 5]  # index 0-7

    # allowed_flights as list of tuples (a, b)
    allowed_flights = [
        (5,7), (7,5),
        (6,4), (4,6),
        (5,4), (4,5),
        (7,4), (4,7),
        (0,7), (7,0),
        (1,7), (7,1),
        (0,1), (1,0),
        (1,4), (4,1),
        (6,5), (5,6),
        (3,4), (4,3),
        (2,7), (7,2),
        (5,0), (0,5),
        (0,4), (4,0),
        (6,7), (7,6),
        (2,6), (6,2),
        (7,3), (3,7),
    ]

    # Create Z3 solver
    solver = Solver()

    # Variables
    cities = [Int(f'city_{i}') for i in range(8)]
    start_days = [Int(f'start_{i}') for i in range(8)]

    # Constraint 1: cities is a permutation of 0-7
    for c in cities:
        solver.add(And(0 <= c, c <= 7))
    solver.add(Distinct(cities))

    # Constraint 2: start_days[0] = 1
    solver.add(start_days[0] == 1)

    # Constraint 3: start_days[i] = start_days[i-1] + duration of previous city
    for i in range(1, 8):
        prev_city = cities[i-1]
        # Compute duration_prev based on prev_city
        duration_prev = If(prev_city == 0, 4,
            If(prev_city == 1, 3,
                If(prev_city == 2, 4,
                    If(prev_city == 3, 2,
                        If(prev_city == 4, 2,
                            If(prev_city == 5, 5,
                                If(prev_city == 6, 3,
                                    If(prev_city == 7, 5, 0)
                                )
                            )
                        )
                    )
                )
            )
        )
        solver.add(start_days[i] == start_days[i-1] + duration_prev)

    # Constraint 4: end_day == 28 (total duration is 28 days)
    last_city = cities[7]
    duration_last = If(last_city == 0, 4,
        If(last_city == 1, 3,
            If(last_city == 2, 4,
                If(last_city == 3, 2,
                    If(last_city == 4, 2,
                        If(last_city == 5, 5,
                            If(last_city == 6, 3,
                                If(last_city == 7, 5, 0)
                            )
                        )
                    )
                )
            )
        )
    )
    solver.add(start_days[7] + duration_last - 1 == 28)

    # Constraint 5: transitions between cities must be allowed
    for i in range(7):
        c1 = cities[i]
        c2 = cities[i+1]
        # Check if (c1, c2) is in allowed_flights
        constraints = []
        for (a, b) in allowed_flights:
            constraints.append(And(c1 == a, c2 == b))
        solver.add(Or(constraints))

    # Constraint 6: Madrid's start day is 20
    for i in range(8):
        solver.add(Implies(cities[i] == 4, start_days[i] == 20))

    # Constraint 7: Stuttgart's start day <=4
    for i in range(8):
        solver.add(Implies(cities[i] == 2, start_days[i] <= 4))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        # Extract cities and start_days
        cities_solution = [model.evaluate(c).as_long() for c in cities]
        start_days_solution = [model.evaluate(s).as_long() for s in start_days]

        # Generate the itinerary
        itinerary = []
        for i in range(8):
            city_index = cities_solution[i]
            city_name = cities_names[city_index]
            start_day = start_days_solution[i]
            duration = durations[city_index]
            end_day = start_day + duration - 1
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})

        # Output as JSON
        import json
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()