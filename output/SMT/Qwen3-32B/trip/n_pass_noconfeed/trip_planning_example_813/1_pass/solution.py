import z3
import json

def main():
    # Define cities and their indexes
    cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
    durations = [5, 3, 2, 2, 3, 3, 5]  # index 0-6

    # Define allowed flights as pairs of city indexes
    allowed_flights = set()
    allowed_flights.add((6,5))
    allowed_flights.add((5,6))
    allowed_flights.add((6,3))
    allowed_flights.add((3,6))
    allowed_flights.add((3,5))
    allowed_flights.add((5,3))
    allowed_flights.add((1,6))
    allowed_flights.add((6,1))
    allowed_flights.add((6,4))
    allowed_flights.add((4,6))
    allowed_flights.add((5,0))
    allowed_flights.add((0,5))
    allowed_flights.add((3,2))
    allowed_flights.add((2,3))
    allowed_flights.add((4,3))
    allowed_flights.add((3,4))
    allowed_flights.add((2,5))
    allowed_flights.add((5,2))

    # Create variables for the sequence of cities (each is an integer 0-6)
    seq = [z3.Int('seq_%d' % i) for i in range(7)]
    solver = z3.Solver()

    # Constraints for permutation: all distinct and in range
    for i in range(7):
        solver.add(z3.And(seq[i] >= 0, seq[i] <= 6))
    solver.add(z3.Distinct(seq))

    # Constraints for allowed flights between consecutive cities
    for i in range(6):
        from_city = seq[i]
        to_city = seq[i+1]
        solver.add(z3.Or([z3.And(from_city == f, to_city == t) for f, t in allowed_flights]))

    # Create start_days and end_days variables
    start_days = [z3.Int('start_day_%d' % i) for i in range(7)]
    end_days = [z3.Int('end_day_%d' % i) for i in range(7)]

    # Constraints for start and end days
    solver.add(start_days[0] == 1)
    for i in range(1, 7):
        solver.add(start_days[i] == start_days[i-1] + durations[seq[i-1]] - 1)
    for i in range(7):
        solver.add(end_days[i] == start_days[i] + durations[seq[i]] - 1)
    solver.add(end_days[6] == 17)

    # Constraints for London (index 3) must include day 9 or 10
    for i in range(7):
        solver.add(z3.Implies(seq[i] == 3,
            z3.Or(
                z3.And(start_days[i] <= 9, 9 <= end_days[i]),
                z3.And(start_days[i] <= 10, 10 <= end_days[i])
            )
        ))

    # Constraints for Stuttgart (index 4) must include day 7, 8, or 9
    for i in range(7):
        solver.add(z3.Implies(seq[i] == 4,
            z3.Or(
                z3.And(start_days[i] <= 7, 7 <= end_days[i]),
                z3.And(start_days[i] <= 8, 8 <= end_days[i]),
                z3.And(start_days[i] <= 9, 9 <= end_days[i])
            )
        ))

    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract the sequence
        sequence = [model.evaluate(seq[i]).as_long() for i in range(7)]
        # Extract start_days and end_days
        start_days_vals = [model.evaluate(start_days[i]).as_long() for i in range(7)]
        end_days_vals = [model.evaluate(end_days[i]).as_long() for i in range(7)]

        # Build the itinerary
        itinerary = []
        for i in range(7):
            city = cities[sequence[i]]
            start = start_days_vals[i]
            end = end_days_vals[i]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})

        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()