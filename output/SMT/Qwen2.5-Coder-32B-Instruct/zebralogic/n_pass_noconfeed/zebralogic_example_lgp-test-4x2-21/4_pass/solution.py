from z3 import *

def solve_puzzle():
    # Define variables
    names = ['Eric', 'Arnold', 'Alice', 'Peter']
    styles = ['craftsman', 'colonial', 'ranch', 'victorian']
    houses = [1, 2, 3, 4]

    # Create symbolic variables
    name_vars = {house: Int(f'name_{house}') for house in houses}
    style_vars = {house: Int(f'style_{house}') for house in houses}

    # Create solver
    solver = Solver()

    # Add constraints for unique values
    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([style_vars[house] for house in houses]))

    # Map names and styles to integers
    name_map = {name: i for i, name in enumerate(names)}
    style_map = {style: i for i, style in enumerate(styles)}

    # Add constraints based on clues
    solver.add(name_vars[2] == name_map['Alice'])  # Alice lives in house 2

    # Peter lives in the ranch style house
    peter_house = Int('peter_house')
    solver.add(peter_house >= 1)
    solver.add(peter_house <= 4)
    solver.add(name_vars[peter_house] == name_map['Peter'])
    solver.add(style_vars[peter_house] == style_map['ranch'])

    # Arnold lives in the craftsman style house
    arnold_house = Int('arnold_house')
    solver.add(arnold_house >= 1)
    solver.add(arnold_house <= 4)
    solver.add(name_vars[arnold_house] == name_map['Arnold'])
    solver.add(style_vars[arnold_house] == style_map['craftsman'])

    # Alice lives in the craftsman style house (already set to house 2)
    solver.add(style_vars[2] == style_map['craftsman'])

    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for house in houses:
            name = names[model.evaluate(name_vars[house]).as_long()]
            style = styles[model.evaluate(style_vars[house]).as_long()]
            solution.append([str(house), name, style])

        return {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": solution
            }
        }
    else:
        return None

# Solve the puzzle and print the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))