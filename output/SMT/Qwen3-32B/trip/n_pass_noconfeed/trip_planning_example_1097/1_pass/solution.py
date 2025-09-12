from z3 import *
import json

def main():
    cities = ['Reykjavik', 'Riga', 'Oslo', 'Lyon', 'Dubrovnik', 'Madrid', 'Warsaw', 'London']
    durations = [4, 2, 3, 5, 2, 2, 4, 3]  # index 0 to 7

    allowed_pairs = [
        (0,6), (6,0),
        (2,5), (5,2),
        (6,1), (1,6),
        (3,7), (7,3),
        (5,7), (7,5),
        (6,7), (7,6),
        (0,5), (5,0),
        (6,2), (2,6),
        (2,4), (4,2),
        (2,0), (0,2),
        (1,2), (2,1),
        (2,3), (3,2),
        (2,7), (7,2),
        (7,0), (0,7),
        (6,5), (5,6),
        (5,3), (3,5),
        (4,5), (5,4),
    ]
    allowed_flights = set(allowed_pairs)

    solver = Solver()

    # Variables for the sequence of cities (indices)
    seq = [Int(f'seq_{i}') for i in range(8)]
    # Variables for the start days of each position
    start_days = [Int(f'start_day_{i}') for i in range(8)]

    # Constraints for sequence to be a permutation
    solver.add(Distinct(seq))
    for i in range(8):
        solver.add(And(0 <= seq[i], seq[i] <= 7))

    # Constraints for start_days
    solver.add(start_days[0] == 1)
    for i in range(1, 8):
        prev_city = seq[i-1]
        duration_prev = durations[prev_city]
        solver.add(start_days[i] == start_days[i-1] + duration_prev)

    # Constraints for Riga (index 1) to have start_day 4
    for i in range(8):
        solver.add(Implies(seq[i] == 1, start_days[i] == 4))

    # Constraints for Dubrovnik (index 4) to have start_day 7
    for i in range(8):
        solver.add(Implies(seq[i] == 4, start_days[i] == 7))

    # Constraint for last city's start day + duration = 18
    solver.add(start_days[7] + durations[seq[7]] == 18)

    # Transition constraints between consecutive cities
    for i in range(7):
        transitions = []
        for a, b in allowed_flights:
            transitions.append(And(seq[i] == a, seq[i+1] == b))
        solver.add(Or(transitions))

    if solver.check() == sat:
        model = solver.model()
        # Extract the sequence
        sequence = [model.evaluate(seq[i]).as_long() for i in range(8)]
        # Extract start_days
        start_days_vals = [model.evaluate(start_days[i]).as_long() for i in range(8)]
        # Now, generate the itinerary
        itinerary = []
        for i in range(8):
            city_idx = sequence[i]
            city = cities[city_idx]
            start = start_days_vals[i]
            duration = durations[city_idx]
            end = start + duration - 1
            day_range = f"Day {start}-Day {end}"
            itinerary.append({"day_range": day_range, "place": city})
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()