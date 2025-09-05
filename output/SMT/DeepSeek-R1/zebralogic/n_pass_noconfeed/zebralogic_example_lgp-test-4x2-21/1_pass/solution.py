import json
from z3 import *

def main():
    # Create solver
    solver = Solver()

    # Define the attributes
    names = ['Eric', 'Arnold', 'Alice', 'Peter']
    styles = ['craftsman', 'colonial', 'ranch', 'victorian']

    # Create mappings for each house position (1-4)
    name_vars = [Int(f'name_{i}') for i in range(1,5)]
    style_vars = [Int(f'style_{i}') for i in range(1,5)]

    # Constraints for each variable to be within 0-3 (indexes of the attributes)
    for i in range(4):
        solver.add(name_vars[i] >= 0, name_vars[i] < 4)
        solver.add(style_vars[i] >= 0, style_vars[i] < 4)

    # All names and styles are distinct
    solver.add(Distinct(name_vars))
    solver.add(Distinct(style_vars))

    # Clue 1: Alice is in the second house (Alice is index 2 in names)
    solver.add(name_vars[1] == 2)

    # Clue 2: Victorian house directly left of Peter
    # Victorian index is 3, Peter index is 3 in names
    for i in range(3):  # Houses 1-3 can be left of someone
        solver.add(Implies(style_vars[i] == 3, name_vars[i+1] == 3))

    # Clue 3: Peter is right of ranch-style home
    # Find ranch position (index 2) and Peter position (index 3)
    ranch_pos = Int('ranch_pos')
    peter_pos = Int('peter_pos')
    solver.add(ranch_pos >= 0, ranch_pos < 4)
    solver.add(peter_pos >= 0, peter_pos < 4)
    # Assign positions
    for i in range(4):
        solver.add(Implies(style_vars[i] == 2, ranch_pos == i))
        solver.add(Implies(name_vars[i] == 3, peter_pos == i))
    solver.add(peter_pos > ranch_pos)

    # Clue 4: Arnold is right of Craftsman-style house
    # Craftsman index is 0, Arnold index is 1 in names
    craftsman_pos = Int('craftsman_pos')
    arnold_pos = Int('arnold_pos')
    solver.add(craftsman_pos >= 0, craftsman_pos < 4)
    solver.add(arnold_pos >= 0, arnold_pos < 4)
    for i in range(4):
        solver.add(Implies(style_vars[i] == 0, craftsman_pos == i))
        solver.add(Implies(name_vars[i] == 1, arnold_pos == i))
    solver.add(arnold_pos > craftsman_pos)

    # Clue 5: Craftsman house is Alice -> already handled by Clue 1 and fixed style for house 2
    solver.add(style_vars[1] == 0)  # craftsman is index 0

    # Check and get solution
    if solver.check() == sat:
        model = solver.model()
        result = []
        for i in range(4):
            name_index = model.eval(name_vars[i]).as_long()
            style_index = model.eval(style_vars[i]).as_long()
            result.append([str(i+1), names[name_index], styles[style_index]])
        
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()