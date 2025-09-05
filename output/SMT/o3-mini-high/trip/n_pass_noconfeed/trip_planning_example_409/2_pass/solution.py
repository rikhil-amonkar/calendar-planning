from z3 import *
import json

def main():
    solver = Solver()

    city_names = {0: "Hamburg", 1: "Zurich", 2: "Helsinki", 3: "Bucharest", 4: "Split"}
    fixed_durations = {0: 2, 1: 3, 2: 2, 3: 2, 4: 7}

    num_segments = 5

    cities = [Int(f"city_{i}") for i in range(num_segments)]
    for c in cities:
        solver.add(c >= 0, c <= 4)
    solver.add(Distinct(cities))

    durs = [Int(f"dur_{i}") for i in range(num_segments)]
    for i in range(num_segments):
        solver.add(
            If(cities[i] == 0, durs[i] == fixed_durations[0],
            If(cities[i] == 1, durs[i] == fixed_durations[1],
            If(cities[i] == 2, durs[i] == fixed_durations[2],
            If(cities[i] == 3, durs[i] == fixed_durations[3],
            If(cities[i] == 4, durs[i] == fixed_durations[4],
               False))))))  # Added an extra closing parenthesis

    starts = [Int(f"start_{i}") for i in range(num_segments)]
    ends   = [Int(f"end_{i}") for i in range(num_segments)]

    solver.add(starts[0] == 1)
    for i in range(num_segments):
        solver.add(ends[i] == starts[i] + durs[i] - 1)
        if i > 0:
            solver.add(starts[i] == ends[i-1])
    solver.add(ends[num_segments - 1] == 12)

    for i in range(num_segments):
        solver.add(Implies(cities[i] == 1, starts[i] <= 3))

    for i in range(num_segments):
        solver.add(Implies(cities[i] == 4, starts[i] == 4))

    def flight_allowed(a, b):
        return Or(
            And(a == 0, b == 1), And(a == 1, b == 0),
            And(a == 0, b == 2), And(a == 2, b == 0),
            And(a == 0, b == 3), And(a == 3, b == 0),
            And(a == 0, b == 4), And(a == 4, b == 0),
            And(a == 1, b == 2), And(a == 2, b == 1),
            And(a == 1, b == 3), And(a == 3, b == 1),
            And(a == 1, b == 4), And(a == 4, b == 1),
            And(a == 2, b == 4), And(a == 4, b == 2)
        )

    for i in range(num_segments - 1):
        solver.add(flight_allowed(cities[i], cities[i+1]))

    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_segments):
            s_val = model[starts[i]].as_long()
            e_val = model[ends[i]].as_long()
            city_val = model[cities[i]].as_long()
            itinerary.append({
                "day_range": f"Day {s_val}-{e_val}",
                "place": city_names[city_val]
            })
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": []}

    print(json.dumps(result))

if __name__ == "__main__":
    main()