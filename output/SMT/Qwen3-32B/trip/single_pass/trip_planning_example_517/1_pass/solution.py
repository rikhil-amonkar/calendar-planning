from z3 import *
import json

def main():
    solver = Solver()

    # Define cities as integers 0-4
    # 0: Bucharest, 1: Warsaw, 2: Stuttgart, 3: Copenhagen, 4: Dubrovnik
    c = [Int(f'c{i}') for i in range(5)]

    # Each city is between 0-4 and all distinct
    solver.add([And(0 <= c[i], c[i] <= 4) for i in range(5)])
    solver.add(Distinct(c))

    # Durations for each city in the sequence
    d = [Int(f'd{i}') for i in range(5)]

    # Define d[i] based on c[i]
    for i in range(5):
        solver.add(
            If(c[i] == 0, d[i] == 6,
            If(c[i] == 1, d[i] == 2,
            If(c[i] == 2, d[i] == 7,
            If(c[i] == 3, d[i] == 3,
               d[i] == 5
            )))))

    # Compute start and end days for each stay
    start = [Int(f'start{i}') for i in range(5)]
    end = [Int(f'end{i}') for i in range(5)]

    # start_0 is 1
    solver.add(start[0] == 1)
    solver.add(end[0] == d[0])

    for i in range(1, 5):
        solver.add(start[i] == end[i-1])
        solver.add(end[i] == start[i] + d[i] - 1)

    # Constraints for day 7 and day 13 being in Stuttgart (code 2)
    for day in [7, 13]:
        for i in range(5):
            solver.add(Implies(And(start[i] <= day, day <= end[i]), c[i] == 2))

    # Bucharest (0) must have at least one day between 1-6
    bucharest_wedding = []
    for i in range(5):
        bucharest_wedding.append(And(start[i] <= 6, end[i] >= 1, c[i] == 0))
    solver.add(Or(bucharest_wedding))

    # Direct flight constraints between consecutive cities
    allowed_pairs = [
        (0, 1), (1, 0),  # Bucharest-Warsaw
        (0, 3), (3, 0),  # Bucharest-Copenhagen
        (1, 2), (2, 1),  # Warsaw-Stuttgart
        (1, 3), (3, 1),  # Warsaw-Copenhagen
        (2, 3), (3, 2),  # Stuttgart-Copenhagen
        (3, 4), (4, 3),  # Copenhagen-Dubrovnik
    ]

    for i in range(4):
        constraints = []
        for a, b in allowed_pairs:
            constraints.append(And(c[i] == a, c[i+1] == b))
        solver.add(Or(constraints))

    if solver.check() == sat:
        model = solver.model()
        cities_sequence = [int(str(model.evaluate(c[i]))) for i in range(5)]
        durations = [model.evaluate(d[i]).as_long() for i in range(5)]
        starts = [model.evaluate(start[i]).as_long() for i in range(5)]
        ends = [model.evaluate(end[i]).as_long() for i in range(5)]

        itinerary = []
        for day in range(1, 20):  # days 1 to 19
            for i in range(5):
                if starts[i] <= day <= ends[i]:
                    city_code = cities_sequence[i]
                    if city_code == 0:
                        city_name = 'Bucharest'
                    elif city_code == 1:
                        city_name = 'Warsaw'
                    elif city_code == 2:
                        city_name = 'Stuttgart'
                    elif city_code == 3:
                        city_name = 'Copenhagen'
                    else:
                        city_name = 'Dubrovnik'
                    itinerary.append({'day': day, 'city': city_name})
                    break

        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()