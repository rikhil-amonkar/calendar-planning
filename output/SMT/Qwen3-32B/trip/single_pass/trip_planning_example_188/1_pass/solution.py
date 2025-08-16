from z3 import *

def main():
    solver = Solver()

    BRUSSELS = "Brussels"
    BARCELONA = "Barcelona"
    SPLIT = "Split"

    city_days = [String(f"day_{i}") for i in range(1, 13)]

    # Day 1 and 2 in Brussels
    solver.add(city_days[0] == BRUSSELS)
    solver.add(city_days[1] == BRUSSELS)

    # Valid transitions
    for i in range(1, 12):
        prev_day = city_days[i-1]
        curr_day = city_days[i]
        allowed = Or(
            And(prev_day == BRUSSELS, curr_day == BARCELONA),
            And(prev_day == BARCELONA, curr_day == BRUSSELS),
            And(prev_day == BARCELONA, curr_day == SPLIT),
            And(prev_day == SPLIT, curr_day == BARCELONA),
        )
        solver.add(Or(prev_day == curr_day, allowed))

    # Count for Brussels
    count_br = Sum([If(city_days[i] == BRUSSELS, 1, 0) for i in range(12)])
    arrivals_br = Sum([If(And(city_days[i] == BRUSSELS, city_days[i-1] != BRUSSELS), 1, 0) for i in range(1, 12)])
    total_br = count_br + arrivals_br
    solver.add(total_br == 2)

    # Count for Barcelona
    count_bar = Sum([If(city_days[i] == BARCELONA, 1, 0) for i in range(12)])
    arrivals_bar = Sum([If(And(city_days[i] == BARCELONA, city_days[i-1] != BARCELONA), 1, 0) for i in range(1, 12)])
    total_bar = count_bar + arrivals_bar
    solver.add(total_bar == 7)

    # Count for Split
    count_split = Sum([If(city_days[i] == SPLIT, 1, 0) for i in range(12)])
    arrivals_split = Sum([If(And(city_days[i] == SPLIT, city_days[i-1] != SPLIT), 1, 0) for i in range(1, 12)])
    total_split = count_split + arrivals_split
    solver.add(total_split == 5)

    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(12):
            day = i + 1
            city = model.eval(city_days[i]).as_string()
            itinerary.append({"day": day, "city": city})
        import json
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()