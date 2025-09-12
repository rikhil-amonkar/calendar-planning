from z3 import *

def solve_puzzle():
    # Define the solver
    solver = Solver()

    # Define variables
    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]
    houses = range(1, 6)

    # Create dictionaries to map names and children to their respective house numbers
    name_to_house = {name: Int(f"{name}_house") for name in names}
    child_to_house = {child: Int(f"{child}_house") for child in children}

    # Add constraints for house numbers (must be between 1 and 5)
    for var in list(name_to_house.values()) + list(child_to_house.values()):
        solver.add(var >= 1, var <= 5)

    # All houses must be distinct
    solver.add(Distinct(list(name_to_house.values())))
    solver.add(Distinct(list(child_to_house.values())))

    # Clue 3: The person's child is named Fred is in the second house.
    solver.add(child_to_house["Fred"] == 2)

    # Clue 7: The person's child is named Fred is directly left of the person's child is named Bella.
    solver.add(child_to_house["Fred"] + 1 == child_to_house["Bella"])

    # Clue 1: Bob is somewhere to the left of the person's child is named Samantha.
    solver.add(name_to_house["Bob"] < child_to_house["Samantha"])

    # Clue 2: The person who is the mother of Timothy is somewhere to the left of the person's child is named Samantha.
    solver.add(name_to_house["Timothy"] < child_to_house["Samantha"])

    # Clue 4: There is one house between Alice and the person's child is named Samantha.
    solver.add(Abs(name_to_house["Alice"] - child_to_house["Samantha"]) == 2)

    # Clue 5: Eric is not in the third house.
    solver.add(name_to_house["Eric"] != 3)

    # Clue 6: Bob is not in the third house.
    solver.add(name_to_house["Bob"] != 3)

    # Clue 8: The person's child is named Samantha is somewhere to the left of Peter.
    solver.add(child_to_house["Samantha"] < name_to_house["Peter"])

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Children"],
                "rows": []
            }
        }
        house_occupants = {house: {"Name": None, "Children": None} for house in houses}

        for name, house_var in name_to_house.items():
            house_value = model[house_var].as_long()
            house_occupants[house_value]["Name"] = name

        for child, house_var in child_to_house.items():
            house_value = model[house_var].as_long()
            house_occupants[house_value]["Children"] = child

        for house in houses:
            solution["solution"]["rows"].append([str(house), house_occupants[house]["Name"], house_occupants[house]["Children"]])

        return solution
    else:
        return None

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))