from z3 import *

def main():
    solver = Solver()

    # Define the sequence of cities: c0, c1, c2, c3, c4
    cities = [Int(f'c{i}') for i in range(5)]

    # Define flight days
    d1, d2, d3, d4 = Ints('d1 d2 d3 d4')

    # Add constraints for flight days
    solver.add(And(1 <= d1, d1 < d2, d2 < d3, d3 < d4, d4 <= 12))

    # Add constraint for Reykjavik (4) being the last city
    solver.add(cities[4] == 4)

    # Add constraint for d4=10
    solver.add(d4 == 10)

    # Add constraint for Reykjavik's duration: 12 -d4 +1 == 3
    solver.add(12 - d4 + 1 == 3)  # which is already satisfied by d4=10

    # required_days for each city (0-4: Geneva, Split, Helsinki, Vilnius, Reykjavik)
    required_days = [6, 2, 2, 3, 3]

    # For each position, add duration constraints
    solver.add(d1 == required_days[cities[0]])
    solver.add((d2 - d1) + 1 == required_days[cities[1]])
    solver.add((d3 - d2) + 1 == required_days[cities[2]])
    solver.add((d4 - d3) + 1 == required_days[cities[3]])
    solver.add(12 - d4 + 1 == required_days[cities[4]])

    # Add constraints for allowed connections between consecutive cities
    connections = {
        0: [1, 2],  # Geneva to Split, Helsinki
        1: [0, 2, 3],  # Split to Geneva, Helsinki, Vilnius
        2: [0, 1, 3, 4],  # Helsinki to Geneva, Split, Vilnius, Reykjavik
        3: [1, 2],  # Vilnius to Split, Helsinki
        4: [2],  # Reykjavik to Helsinki
    }

    for i in range(4):
        current_city = cities[i]
        next_city = cities[i+1]
        # Add constraint that next_city is in the allowed connections of current_city
        allowed = []
        for conn in connections[current_city]:
            allowed.append(next_city == conn)
        solver.add(Or(allowed))

    # Add constraint that all cities are unique
    solver.add(Distinct(cities))

    # Add constraints for Vilnius (3) being in the sequence and its flight days
    for i in range(5):
        if i == 0:
            solver.add(If(cities[i] == 3, d1 == 3, True))
        elif i == 1:
            solver.add(If(cities[i] == 3, And(d1 == 7, d2 == 9), True))
        elif i == 2:
            solver.add(If(cities[i] == 3, And(d2 == 7, d3 == 9), True))
        elif i == 3:
            solver.add(If(cities[i] == 3, And(d3 == 7, d4 == 9), True))
        elif i == 4:
            solver.add(If(cities[i] == 3, True, True))  # no-op

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        # Extract cities and flight days
        cities_values = [model.eval(c).as_long() for c in cities]
        d1_val = model.eval(d1).as_long()
        d2_val = model.eval(d2).as_long()
        d3_val = model.eval(d3).as_long()
        d4_val = model.eval(d4).as_long()

        # Map city numbers to names
        city_names = {
            0: "Geneva",
            1: "Split",
            2: "Helsinki",
            3: "Vilnius",
            4: "Reykjavik"
        }

        # Generate the itinerary
        itinerary = []
        for day in range(1, 13):
            if day <= d1_val:
                city = cities_values[0]
            elif day <= d2_val:
                city = cities_values[1]
            elif day <= d3_val:
                city = cities_values[2]
            elif day <= d4_val:
                city = cities_values[3]
            else:
                city = cities_values[4]
            itinerary.append({
                "day": day,
                "city": city_names[city]
            })

        # Print the JSON
        import json
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()