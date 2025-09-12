from z3 import *
import json

def main():
    cities = ['Mykonos', 'Nice', 'Zurich', 'Prague', 'Bucharest', 'Riga', 'Valencia']
    city_durations = {
        0: 3,  # Mykonos
        1: 2,  # Nice
        2: 5,  # Zurich
        3: 3,  # Prague
        4: 5,  # Bucharest
        5: 5,  # Riga
        6: 5,  # Valencia
    }

    allowed_transitions = {
        (0, 1), (1, 0),
        (0, 2), (2, 0),
        (3, 4), (4, 3),
        (6, 4), (4, 6),
        (2, 3), (3, 2),
        (5, 1), (1, 5),
        (2, 5), (5, 2),
        (2, 4), (4, 2),
        (2, 6), (6, 2),
        (4, 5), (5, 4),
        (3, 5), (5, 3),
        (3, 6), (6, 3),
        (2, 1), (1, 2),
    }

    solver = Solver()
    order = [Int(f'order_{i}') for i in range(7)]
    start_days = [Int(f'start_{i}') for i in range(7)]

    # Constraints for order variables
    solver.add(order[0] == 0)  # Mykonos is first
    solver.add(Distinct(order))

    # Constraints for start_days
    solver.add(start_days[0] == 1)

    for i in range(1, 7):
        prev_city = order[i - 1]
        duration_prev = city_durations[prev_city]
        solver.add(start_days[i] == start_days[i - 1] + duration_prev - 1)

    # Constraints for Prague's start day
    for i in range(7):
        solver.add(Implies(order[i] == 3, start_days[i] == 7))

    # Constraints for transitions between consecutive cities
    for i in range(6):
        current = order[i]
        next_city = order[i + 1]
        allowed_pairs = []
        for a, b in allowed_transitions:
            allowed_pairs.append(And(current == a, next_city == b))
        solver.add(Or(allowed_pairs))

    # Constraint for last day
    last_city = order[6]
    duration_last = city_durations[last_city]
    end_day_last = start_days[6] + duration_last - 1
    solver.add(end_day_last == 22)

    if solver.check() == sat:
        model = solver.model()
        order_values = [model.evaluate(order[i]).as_long() for i in range(7)]
        start_days_values = [model.evaluate(start_days[i]).as_long() for i in range(7)]

        itinerary = []
        for i in range(7):
            city_code = order_values[i]
            city_name = cities[city_code]
            start = start_days_values[i]
            duration = city_durations[city_code]
            end = start + duration - 1
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city_name})

        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()