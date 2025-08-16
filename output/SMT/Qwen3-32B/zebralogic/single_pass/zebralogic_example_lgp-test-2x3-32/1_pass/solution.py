from z3 import *
import json

def solve_puzzle():
    # Define EnumSorts
    name_sort, (Eric, Arnold) = EnumSort('name_sort', ['Eric', 'Arnold'])
    birthday_sort, (April, September) = EnumSort('birthday_sort', ['April', 'September'])
    color_sort, (Yellow, Red) = EnumSort('color_sort', ['Yellow', 'Red'])

    # Variables for each house
    name1 = Const('name1', name_sort)
    name2 = Const('name2', name_sort)
    birthday1 = Const('birthday1', birthday_sort)
    birthday2 = Const('birthday2', birthday_sort)
    color1 = Const('color1', color_sort)
    color2 = Const('color2', color_sort)

    solver = Solver()

    # Add constraints
    solver.add(birthday1 == April)  # Clue 2
    solver.add(color1 != Yellow)   # Clue 3
    # Clue 1: Eric loves yellow
    solver.add(Implies(name1 == Eric, color1 == Yellow))
    solver.add(Implies(name2 == Eric, color2 == Yellow))
    # Uniqueness constraints
    solver.add(name1 != name2)
    solver.add(birthday1 != birthday2)
    solver.add(color1 != color2)

    if solver.check() == sat:
        model = solver.model()

        def get_str(var):
            return model.eval(var).decl().name()

        row1 = ["1", get_str(name1), get_str(birthday1), get_str(color1)]
        row2 = ["2", get_str(name2), get_str(birthday2), get_str(color2)]

        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Color"],
                "rows": [row1, row2]
            }
        }

        print(json.dumps(solution))

    else:
        print("No solution found.")

solve_puzzle()