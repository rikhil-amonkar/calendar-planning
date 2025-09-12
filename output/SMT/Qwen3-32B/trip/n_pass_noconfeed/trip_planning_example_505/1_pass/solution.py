import z3
import json

def main():
    solver = z3.Solver()

    # Cities: 0-Prague, 1-Stuttgart, 2-Split, 3-Krakow, 4-Florence
    order = [z3.Int(f'order_{i}') for i in range(5)]
    durations = [4, 2, 2, 2, 2]  # durations for each city index

    # Constraints: order is a permutation of 0-4
    solver.add(z3.Distinct(order))
    for city in order:
        solver.add(z3.And(0 <= city, city <= 4))

    # Start days
    start_day = [z3.Int(f'start_day_{i}') for i in range(5)]
    solver.add(start_day[0] == 1)
    for i in range(1, 5):
        prev_city = order[i-1]
        add_3_if_prague = z3.If(prev_city == 0, 3, 1)
        solver.add(start_day[i] == start_day[i-1] + add_3_if_prague)

    # Constraints for Stuttgart (1) start day == 2 and Split (2) start day ==3
    for i in range(5):
        solver.add(z3.Implies(order[i] == 1, start_day[i] == 2))
        solver.add(z3.Implies(order[i] == 2, start_day[i] == 3))

    # Allowed transitions
    allowed_transitions = [
        (0,4), (4,0),
        (1,2), (2,1),
        (3,1), (1,3),
        (3,2), (2,3),
        (2,0), (0,2),
        (3,0), (0,3),
    ]

    for i in range(4):
        current = order[i]
        next_city = order[i+1]
        conditions = [z3.And(current == a, next_city == b) for a, b in allowed_transitions]
        solver.add(z3.Or(conditions))

    # Check if satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        order_values = [model.evaluate(order[i]).as_long() for i in range(5)]
        start_day_values = [model.evaluate(start_day[i]).as_long() for i in range(5)]

        city_names = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
        itinerary = []
        for i in range(5):
            city_idx = order_values[i]
            city_name = city_names[city_idx]
            start = start_day_values[i]
            duration = durations[city_idx]
            end = start + duration - 1
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city_name})

        # Output JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()