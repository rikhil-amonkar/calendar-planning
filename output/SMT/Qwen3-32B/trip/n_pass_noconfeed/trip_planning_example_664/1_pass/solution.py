from z3 import *
import json

def main():
    # Define cities as integers 0-5
    # 0: Tallinn, 1: Bucharest, 2: Seville, 3: Stockholm, 4: Munich, 5: Milan
    durations = {0: 2, 1: 4, 2: 5, 3: 5, 4: 5, 5: 2}
    allowed_transitions = [
        (5,3), (3,5),  # Milan-Stoc
        (4,3), (3,4),  # Munich-Stoc
        (1,4), (4,1),  # Bucharest-Munich
        (4,2), (2,4),  # Munich-Seville
        (3,0), (0,3),  # Stoc-Tallinn
        (4,5), (5,4),  # Munich-Milan
        (4,0), (0,4),  # Munich-Tallinn
        (2,5), (5,2)   # Seville-Milan
    ]

    # Create variables for the sequence of cities
    pos = [Int(f'pos_{i}') for i in range(6)]
    s = [Int(f's_{i}') for i in range(6)]

    solver = Solver()

    # Add constraints for permutation
    solver.add(Distinct(pos))
    for p in pos:
        solver.add(And(0 <= p, p <= 5))

    # Add transition constraints
    for i in range(5):
        from_c = pos[i]
        to_c = pos[i+1]
        transitions = []
        for a, b in allowed_transitions:
            transitions.append(And(from_c == a, to_c == b))
        solver.add(Or(transitions))

    # Add start day constraints
    solver.add(s[0] == 1)
    for i in range(1, 6):
        prev_city = pos[i-1]
        # Compute duration_prev based on prev_city
        duration_prev = If(prev_city == 0, 2,
                           If(prev_city == 1, 4,
                              If(prev_city == 2, 5,
                                 If(prev_city == 3, 5,
                                    If(prev_city == 4, 5,
                                       If(prev_city == 5, 2, 0))))))
        solver.add(s[i] == s[i-1] + duration_prev - 1)

    # Add time constraints for each city
    for i in range(6):
        # Bucharest (1) constraint: s[i] <=4
        solver.add(Implies(pos[i] == 1, s[i] <= 4))
        # Seville (2) constraint: 4 <= s[i] <=12
        solver.add(Implies(pos[i] == 2, And(s[i] >= 4, s[i] <= 12)))
        # Munich (4) constraint: s[i] <=8
        solver.add(Implies(pos[i] == 4, s[i] <= 8))

    if solver.check() == sat:
        model = solver.model()
        # Extract the sequence and start days
        sequence = [model.evaluate(pos[i]).as_long() for i in range(6)]
        start_days = [model.evaluate(s[i]).as_long() for i in range(6)]
        # Generate the itinerary
        cities_list = ['Tallinn', 'Bucharest', 'Seville', 'Stockholm', 'Munich', 'Milan']
        itinerary = []
        for i in range(6):
            city_code = sequence[i]
            city_name = cities_list[city_code]
            start_day = start_days[i]
            duration = durations[city_code]
            end_day = start_day + duration - 1
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()