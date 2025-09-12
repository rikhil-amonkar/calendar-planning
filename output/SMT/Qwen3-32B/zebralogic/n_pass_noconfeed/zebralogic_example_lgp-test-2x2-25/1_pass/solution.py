import json
from z3 import *

def main():
    # Define variables for each house's attributes
    name1 = Int('name1')
    name2 = Int('name2')
    vacation1 = Int('vacation1')
    vacation2 = Int('vacation2')

    solver = Solver()

    # Possible values for names (0: Arnold, 1: Eric) and vacations (0: beach, 1: mountain)
    solver.add(Or(name1 == 0, name1 == 1))
    solver.add(Or(name2 == 0, name2 == 1))
    solver.add(Or(vacation1 == 0, vacation1 == 1))
    solver.add(Or(vacation2 == 0, vacation2 == 1))

    # Uniqueness constraints
    solver.add(name1 != name2)
    solver.add(vacation1 != vacation2)

    # Clue constraints
    solver.add(vacation2 != 0)  # Beach vacation cannot be in house 2
    solver.add(Implies(vacation1 == 0, name2 == 0))  # If house 1 has beach, Arnold is in house 2

    if solver.check() == sat:
        model = solver.model()
        # Extract values from the model
        n1 = model[name1].as_long()
        n2 = model[name2].as_long()
        v1 = model[vacation1].as_long()
        v2 = model[vacation2].as_long()

        # Mapping integers to human-readable values
        name_map = {0: 'Arnold', 1: 'Eric'}
        vacation_map = {0: 'beach', 1: 'mountain'}

        # Construct the solution rows
        rows = [
            ["1", name_map[n1], vacation_map[v1]],
            ["2", name_map[n2], vacation_map[v2]]
        ]

        # Format the solution as required JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }

        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()