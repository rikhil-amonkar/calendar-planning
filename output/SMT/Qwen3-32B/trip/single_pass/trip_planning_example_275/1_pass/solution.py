import json
from z3 import *

def main():
    # Define cities: 0: Vilnius, 1: Split, 2: Madrid, 3: Santorini
    cities = [0, 1, 2, 3]
    allowed_transitions = [(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)]

    # Create solver
    solver = Solver()

    # Define variables for the sequence of cities (4 cities)
    c = [Int(f'c{i}') for i in range(4)]

    # Each city in the sequence must be one of the four cities
    for ci in c:
        solver.add(Or([ci == city for city in cities]))

    # Consecutive transitions must be allowed
    for i in range(3):
        current = c[i]
        next_city = c[i + 1]
        # Add constraint that (current, next_city) is in allowed_transitions
        transition_constraints = []
        for a, b in allowed_transitions:
            transition_constraints.append(And(current == a, next_city == b))
        solver.add(Or(*transition_constraints))

    # Define durations for each city in the sequence
    d = [Int(f'd{i}') for i in range(4)]

    # Required durations
    solver.add(d[0] == 4)  # Vilnius
    solver.add(d[1] == 5)  # Split
    solver.add(d[2] == 6)  # Madrid
    solver.add(d[3] == 2)  # Santorini

    # Constraint for arrival day of Santorini
    solver.add(d[0] + d[1] + d[2] - 2 == 13)

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        sequence = [model.evaluate(c[i]).as_long() for i in range(4)]
        durations = [model.evaluate(d[i]).as_long() for i in range(4)]

        # Calculate start and end days for each city
        start_days = [1]
        end_days = [start_days[0] + durations[0] - 1]
        for i in range(1, 4):
            start_days.append(end_days[i - 1])
            end_days.append(start_days[i] + durations[i] - 1)

        # Generate the itinerary
        itinerary = []
        for day in range(1, 15):
            active_cities = []
            for i in range(4):
                if start_days[i] <= day <= end_days[i]:
                    city_name = ""
                    if sequence[i] == 0:
                        city_name = "Vilnius"
                    elif sequence[i] == 1:
                        city_name = "Split"
                    elif sequence[i] == 2:
                        city_name = "Madrid"
                    elif sequence[i] == 3:
                        city_name = "Santorini"
                    active_cities.append(city_name)
            itinerary.append({"day": day, "city": active_cities if len(active_cities) > 1 else active_cities[0]})

        # Output the JSON-formatted result
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()