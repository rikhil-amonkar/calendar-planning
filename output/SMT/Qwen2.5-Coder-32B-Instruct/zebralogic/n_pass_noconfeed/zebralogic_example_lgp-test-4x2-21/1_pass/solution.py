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
    solver.add(name_vars[2] == name_map['Alice'])
    solver.add(style_vars[house] == style_map['victorian'] for house in houses if house < 4).then(solver.add(name_vars[house + 1] == name_map['Peter']))
    solver.add(Or([And(style_vars[i] == style_map['ranch'], name_vars[j] == name_map['Peter']) for i in range(4) for j in range(i + 1, 4)]))
    solver.add(Or([And(style_vars[i] == style_map['craftsman'], name_vars[j] == name_map['Arnold']) for i in range(4) for j in range(i + 1, 4)]))
    solver.add(style_vars[house] == style_map['craftsman'] for house in houses if name_vars[house] == name_map['Alice'])

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