from z3 import *
import json

def solve_puzzle():
    # Define EnumSorts for names and vacations
    Name, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    Vacation, (beach, mountain) = EnumSort('Vacation', ['beach', 'mountain'])

    # Variables for each house
    name1 = Const('name1', Name)
    name2 = Const('name2', Name)
    vacation1 = Const('vacation1', Vacation)
    vacation2 = Const('vacation2', Vacation)

    solver = Solver()

    # Constraints for unique names and vacations
    solver.add(name1 != name2)
    solver.add(vacation1 != vacation2)

    # Clue: Arnold is to the right of the beach lover
    beach_house = If(vacation1 == beach, 1, 2)
    arnold_house = If(name1 == Arnold, 1, 2)
    solver.add(beach_house < arnold_house)

    if solver.check() == sat:
        model = solver.model()
        # Extract values for each house
        n1 = model[name1].name()
        v1 = model[vacation1].name()
        n2 = model[name2].name()
        v2 = model[vacation2].name()

        # Construct the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": [
                    ["1", n1, v1],
                    ["2", n2, v2]
                ]
            }
        }
        return json.dumps(solution)
    else:
        return json.dumps({"error": "No solution found"})

# Execute and print the result
print(solve_puzzle())