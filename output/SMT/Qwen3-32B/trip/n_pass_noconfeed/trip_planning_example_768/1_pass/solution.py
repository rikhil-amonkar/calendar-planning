from z3 import *
import json

def main():
    solver = Solver()

    # Define cities: 0: Mykonos, 1: Nice, 2: London, 3: Copenhagen, 4: Oslo, 5: Tallinn
    durations = [4, 3, 2, 3, 5, 4]

    # Create variables for the order of cities
    order = [Int(f'order_{i}') for i in range(6)]

    # Add constraints that order is a permutation of 0-5
    for i in range(6):
        solver.add(And(order[i] >= 0, order[i] <= 5))
    solver.add(Distinct(order))

    # Constraint: last city is Nice (1)
    solver.add(order[5] == 1)

    # Create variables for start_day of each city in the order
    start_day = [Int(f'start_day_{i}') for i in range(6)]

    # Create durations_array in Z3
    durations_array = Array('durations_array', IntSort(), IntSort())
    for i in range(6):
        solver.add(durations_array[i] == durations[i])

    # Add constraints for start_day
    solver.add(start_day[0] == 1)
    for i in range(1, 6):
        solver.add(start_day[i] == start_day[i-1] + (durations_array[order[i-1]] - 1))

    # Allowed transitions between cities
    allowed_pairs = [
        (2,3), (3,2),
        (3,5), (5,3),
        (5,4), (4,5),
        (0,2), (2,0),
        (4,1), (1,4),
        (2,1), (1,2),
        (0,1), (1,0),
        (2,4), (4,2),
        (3,1), (1,3),
        (3,4), (4,3),
    ]

    # Add transition constraints
    for i in range(5):
        current = order[i]
        next_city = order[i+1]
        constraints = []
        for a, b in allowed_pairs:
            constraints.append(And(current == a, next_city == b))
        solver.add(Or(constraints))

    # Add constraint for Oslo (4) to be between day 10-14
    for i in range(6):
        solver.add(Implies(order[i] == 4, And(start_day[i] >= 6, start_day[i] <= 13)))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        # Extract order and start_day values
        order_values = [model.evaluate(order[i]).as_long() for i in range(6)]
        start_day_values = [model.evaluate(start_day[i]).as_long() for i in range(6)]

        # Map city indices to names
        cities_names = {0: 'Mykonos', 1: 'Nice', 2: 'London', 3: 'Copenhagen', 4: 'Oslo', 5: 'Tallinn'}
        itinerary = []
        for i in range(6):
            city_idx = order_values[i]
            city_name = cities_names[city_idx]
            start = start_day_values[i]
            duration = durations[city_idx]
            end = start + duration - 1
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city_name})

        # Output JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()