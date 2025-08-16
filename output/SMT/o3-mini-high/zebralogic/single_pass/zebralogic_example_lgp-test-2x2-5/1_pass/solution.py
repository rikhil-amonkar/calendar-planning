from z3 import Solver, Int, Or, sat
import json

def main():
    # Create the Z3 solver instance
    solver = Solver()

    # For each house, we assign:
    # name: 0 for Eric, 1 for Arnold
    # house style: 0 for victorian, 1 for colonial
    # There are two houses, numbered 1 and 2.
    name1 = Int('name1')
    name2 = Int('name2')
    style1 = Int('style1')
    style2 = Int('style2')

    # Restrict the domains of our variables to be either 0 or 1
    solver.add(Or(name1 == 0, name1 == 1))
    solver.add(Or(name2 == 0, name2 == 1))
    solver.add(Or(style1 == 0, style1 == 1))
    solver.add(Or(style2 == 0, style2 == 1))

    # Enforce uniqueness: each house gets a unique name and a unique style.
    solver.add(name1 != name2)
    solver.add(style1 != style2)

    # Clue 2: Eric is in the first house.
    # Here, we represent Eric as 0.
    solver.add(name1 == 0)

    # Clue 1: The person residing in a Victorian house is somewhere
    # to the left of the person living in a Colonial-style house.
    # With two houses (house 1 is left of house 2), this forces:
    # House 1 must be victorian (0) and House 2 must be colonial (1).
    solver.add(style1 == 0)
    solver.add(style2 == 1)

    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        # Map our integer values back to their meanings.
        mapping_name = {0: "Eric", 1: "Arnold"}
        mapping_style = {0: "victorian", 1: "colonial"}

        house1 = ["1", mapping_name[model[name1].as_long()], mapping_style[model[style1].as_long()]]
        house2 = ["2", mapping_name[model[name2].as_long()], mapping_style[model[style2].as_long()]]

        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": [house1, house2]
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()