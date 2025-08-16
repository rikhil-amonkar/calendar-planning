from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    solver = Solver()

    # Define the houses
    houses = [1, 2, 3, 4]

    # Define the names and colors
    names = ["Peter", "Arnold", "Alice", "Eric"]
    colors = ["yellow", "green", "red", "white"]

    # Create variables for each house's name and color
    name_vars = {house: Int(f"name_{house}") for house in houses}
    color_vars = {house: Int(f"color_{house}") for house in houses}

    # Add constraints for names and colors to be within their respective ranges
    for house in houses:
        solver.add(And(name_vars[house] >= 0, name_vars[house] < len(names)))
        solver.add(And(color_vars[house] >= 0, color_vars[house] < len(colors)))

    # Add constraint that all names and colors are distinct
    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([color_vars[house] for house in houses]))

    # Clue 1: The person whose favorite color is green is in the third house.
    green_index = colors.index("green")
    solver.add(color_vars[3] == green_index)

    # Clue 2: Peter is in the first house.
    peter_index = names.index("Peter")
    solver.add(name_vars[1] == peter_index)

    # Clue 3: There is one house between the person whose favorite color is red and the person who loves yellow.
    red_index = colors.index("red")
    yellow_index = colors.index("yellow")
    # Possible positions for red and yellow: red in 1 and yellow in 3, or red in 2 and yellow in 4
    solver.add(Or(
        And(color_vars[1] == red_index, color_vars[3] == yellow_index),
        And(color_vars[2] == red_index, color_vars[4] == yellow_index)
    ))

    # Clue 4: Arnold is directly left of Eric.
    arnold_index = names.index("Arnold")
    eric_index = names.index("Eric")
    # Arnold is in house i, Eric is in house i+1
    solver.add(Or(
        And(name_vars[1] == arnold_index, name_vars[2] == eric_index),
        And(name_vars[2] == arnold_index, name_vars[3] == eric_index),
        And(name_vars[3] == arnold_index, name_vars[4] == eric_index)
    ))

    # Clue 5: Eric is the person who loves yellow.
    # So in the house where name is Eric, color is yellow
    for house in houses:
        solver.add(Implies(name_vars[house] == eric_index, color_vars[house] == yellow_index))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        solution = {"solution": {"header": ["House", "Name", "Color"], "rows": []}}
        for house in sorted(houses):
            name_val = model.evaluate(name_vars[house]).as_long()
            color_val = model.evaluate(color_vars[house]).as_long()
            solution["solution"]["rows"].append([
                str(house),
                names[name_val],
                colors[color_val]
            ])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Color"], "rows": []}}

# Print the solution as JSON
import json
print(json.dumps(solve_scheduling_problem(), indent=2))