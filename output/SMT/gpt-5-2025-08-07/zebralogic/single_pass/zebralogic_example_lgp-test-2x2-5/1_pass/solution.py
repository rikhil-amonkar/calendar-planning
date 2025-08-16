import json
from z3 import Solver, EnumSort, Const, Distinct, And, Or

def solve():
    # Number of houses
    n = 2

    # Define enum sorts for Names and HouseStyle
    NameSort, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
    HouseStyleSort, (victorian, colonial) = EnumSort('HouseStyle', ['victorian', 'colonial'])

    # Create variables for each house
    names = [Const(f"name_{i+1}", NameSort) for i in range(n)]
    styles = [Const(f"style_{i+1}", HouseStyleSort) for i in range(n)]

    s = Solver()

    # Uniqueness constraints
    s.add(Distinct(names))
    s.add(Distinct(styles))

    # Clue 1: The person residing in a Victorian house is somewhere to the left of the person living in a colonial-style house.
    # Encode as: there exist i < j such that styles[i] == victorian and styles[j] == colonial
    left_of_constraints = []
    for i in range(n):
        for j in range(i + 1, n):
            left_of_constraints.append(And(styles[i] == victorian, styles[j] == colonial))
    s.add(Or(left_of_constraints))

    # Clue 2: Eric is in the first house.
    s.add(names[0] == Eric)

    if s.check() != 1:  # sat == 1
        raise Exception("No solution found")

    m = s.model()

    rows = []
    for i in range(n):
        house_num = str(i + 1)
        name_val = str(m.evaluate(names[i]))
        style_val = str(m.evaluate(styles[i]))
        rows.append([house_num, name_val, style_val])

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }

    print(json.dumps(result))

if __name__ == "__main__":
    solve()