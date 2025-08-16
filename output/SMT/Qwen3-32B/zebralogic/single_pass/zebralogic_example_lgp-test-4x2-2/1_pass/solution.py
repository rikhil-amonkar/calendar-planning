from z3 import *
import json

def main():
    # Define the possible names and styles
    names_list = ['Arnold', 'Peter', 'Eric', 'Alice']
    styles_list = ['victorian', 'ranch', 'colonial', 'craftsman']

    # Create solver
    solver = Solver()

    # Create variables for each house (1-4)
    name = [Int(f'name_{i}') for i in range(1,5)]
    style = [Int(f'style_{i}') for i in range(1,5)]

    # Add constraints that all names are distinct and in 0-3
    solver.add(Distinct(name))
    for n in name:
        solver.add(And(n >= 0, n <= 3))

    # Same for styles
    solver.add(Distinct(style))
    for s in style:
        solver.add(And(s >= 0, s <= 3))

    # Clue 3: Eric (index 2) is in house 3 (index 2 in the list)
    solver.add(name[2] == 2)

    # Clue 1: Eric's house is Craftsman (index 3)
    solver.add(style[2] == 3)

    # Clue 4: Arnold (index 0) is in house 4 (index 3)
    solver.add(name[3] == 0)

    # Clue 5: If a house's style is victorian (0), then name is Alice (3)
    for i in range(4):
        solver.add(Implies(style[i] == 0, name[i] == 3))

    # Clue 2: ranch (1) directly left of victorian (0)
    solver.add(Or(
        And(style[0] == 1, style[1] == 0),
        And(style[1] == 1, style[2] == 0),
        And(style[2] == 1, style[3] == 0)
    ))

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        # Prepare the solution
        rows = []
        for i in range(4):
            house_num = i + 1
            name_idx = model[name[i]].as_long()
            style_idx = model[style[i]].as_long()
            name_str = names_list[name_idx]
            style_str = styles_list[style_idx]
            rows.append([str(house_num), name_str, style_str])
        # Construct the JSON structure
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()