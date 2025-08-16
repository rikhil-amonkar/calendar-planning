import json
from z3 import *

def solve_puzzle():
    # Define sorts (enums) for attributes
    Name, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
    Birthday, (sept, april) = EnumSort('Birthday', ['sept', 'april'])
    Color, (yellow, red) = EnumSort('Color', ['yellow', 'red'])

    # Two houses: index 0 -> House "1", index 1 -> House "2"
    num_houses = 2
    names = [Const(f'name_{i}', Name) for i in range(num_houses)]
    birthdays = [Const(f'birthday_{i}', Birthday) for i in range(num_houses)]
    colors = [Const(f'color_{i}', Color) for i in range(num_houses)]

    s = Solver()

    # Uniqueness constraints for each attribute across houses
    s.add(Distinct(names))
    s.add(Distinct(birthdays))
    s.add(Distinct(colors))

    # Clue 1: Eric is the person who loves yellow (bi-conditional per house)
    for i in range(num_houses):
        s.add(Implies(names[i] == Eric, colors[i] == yellow))
        s.add(Implies(colors[i] == yellow, names[i] == Eric))

    # Clue 2: The person whose birthday is in April is in the first house.
    s.add(birthdays[0] == april)

    # Clue 3: The person who loves yellow is not in the first house.
    s.add(colors[0] != yellow)

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build JSON result
    rows = []
    for i in range(num_houses):
        house_num = str(i + 1)
        n = str(m.eval(names[i]))
        b = str(m.eval(birthdays[i]))
        c = str(m.eval(colors[i]))
        rows.append([house_num, n, b, c])

    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()