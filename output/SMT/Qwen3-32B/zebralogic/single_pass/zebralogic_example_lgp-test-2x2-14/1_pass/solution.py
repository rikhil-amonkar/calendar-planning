import json
from z3 import *

def main():
    solver = Solver()

    # Define EnumSorts for Name and Food
    Name, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
    Food, (pizza, grilled_cheese) = EnumSort('Food', ['pizza', 'grilled cheese'])

    # Variables for each house's attributes
    name1 = Const('name1', Name)
    name2 = Const('name2', Name)
    food1 = Const('food1', Food)
    food2 = Const('food2', Food)

    # Add constraints for uniqueness and clues
    solver.add(name1 != name2)          # Names must be unique
    solver.add(food1 != food2)          # Foods must be unique
    solver.add(food2 == pizza)          # Clue 1: Pizza in the second house
    solver.add(name1 != Arnold)         # Clue 2: Arnold is not in the first house

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        # Extract values from the model
        n1 = model[name1]
        f1 = model[food1]
        n2 = model[name2]
        f2 = model[food2]

        # Format the solution as JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "Food"],
                "rows": [
                    ["1", str(n1), str(f1)],
                    ["2", str(n2), str(f2)]
                ]
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()