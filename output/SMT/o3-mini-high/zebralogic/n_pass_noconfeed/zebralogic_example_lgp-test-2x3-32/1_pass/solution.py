import json
from z3 import Solver, Int, Or, Implies, sat

def main():
    solver = Solver()

    # Define variables for each house
    # House 1 variables
    house1_name = Int("house1_name")    # 0: Eric, 1: Arnold
    house1_birth = Int("house1_birth")  # 0: april, 1: sept
    house1_color = Int("house1_color")  # 0: yellow, 1: red

    # House 2 variables
    house2_name = Int("house2_name")    # 0: Eric, 1: Arnold
    house2_birth = Int("house2_birth")  # 0: april, 1: sept
    house2_color = Int("house2_color")  # 0: yellow, 1: red

    # Domain constraints for all variables (each attribute has two possible values: 0 or 1)
    for var in [house1_name, house1_birth, house1_color, house2_name, house2_birth, house2_color]:
        solver.add(Or(var == 0, var == 1))

    # Uniqueness constraints: each attribute is unique across the houses.
    solver.add(house1_name != house2_name)
    solver.add(house1_birth != house2_birth)
    solver.add(house1_color != house2_color)

    # Clue 2: "The person whose birthday is in April is in the first house."
    # We map april to 0 and sept to 1, so house 1's birthday must be april (0).
    solver.add(house1_birth == 0)

    # Clue 3: "The person who loves yellow is not in the first house."
    # We map yellow to 0 and red to 1, so house 1's color cannot be yellow (0).
    solver.add(house1_color != 0)

    # Clue 1: "Eric is the person who loves yellow."
    # We map Eric to 0 and Arnold to 1. This clue implies that
    # if a house's name is Eric (0), then the color must be yellow (0), and vice versa.
    solver.add(Implies(house1_name == 0, house1_color == 0))
    solver.add(Implies(house1_color == 0, house1_name == 0))
    solver.add(Implies(house2_name == 0, house2_color == 0))
    solver.add(Implies(house2_color == 0, house2_name == 0))

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        # Extract model values
        h1_name_val = model[house1_name].as_long()
        h1_birth_val = model[house1_birth].as_long()
        h1_color_val = model[house1_color].as_long()
        h2_name_val = model[house2_name].as_long()
        h2_birth_val = model[house2_birth].as_long()
        h2_color_val = model[house2_color].as_long()

        # Mappings for human readable attributes
        name_map = {0: "Eric", 1: "Arnold"}
        birthday_map = {0: "april", 1: "sept"}
        color_map = {0: "yellow", 1: "red"}

        # Construct the solution in the required JSON structure
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Color"],
                "rows": [
                    ["1", name_map[h1_name_val], birthday_map[h1_birth_val], color_map[h1_color_val]],
                    ["2", name_map[h2_name_val], birthday_map[h2_birth_val], color_map[h2_color_val]]
                ]
            }
        }
        print(json.dumps(solution))
    else:
        # If no solution is found, output an empty solution structure.
        print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    main()