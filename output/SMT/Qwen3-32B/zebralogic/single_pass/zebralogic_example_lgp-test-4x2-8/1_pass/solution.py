from z3 import *
import json

def main():
    s = Solver()

    # Variables for each house's name and color (0-3)
    name = [Int(f'name_{i+1}') for i in range(4)]
    color = [Int(f'color_{i+1}') for i in range(4)]

    # All names and colors are distinct and in 0-3
    s.add(Distinct(name))
    s.add(Distinct(color))
    for n in name:
        s.add(And(0 <= n, n <= 3))
    for c in color:
        s.add(And(0 <= c, c <= 3))

    # Clue 1: color_3 is green (1)
    s.add(color[2] == 1)

    # Clue 2: name_1 is Peter (0)
    s.add(name[0] == 0)

    # Clue 3: red and yellow with one house between
    red_house = 0
    for i in range(4):
        red_house += If(color[i] == 2, i + 1, 0)
    yellow_house = 0
    for i in range(4):
        yellow_house += If(color[i] == 0, i + 1, 0)
    s.add(Abs(red_house - yellow_house) == 2)

    # Clue 4: Arnold (1) directly left of Eric (3)
    s.add(Or(
        And(name[0] == 1, name[1] == 3),
        And(name[1] == 1, name[2] == 3),
        And(name[2] == 1, name[3] == 3)
    ))

    # Clue 5: Eric's color is yellow
    for i in range(4):
        s.add(Implies(name[i] == 3, color[i] == 0))

    if s.check() == sat:
        model = s.model()
        # Mapping
        name_map = {0: 'Peter', 1: 'Arnold', 2: 'Alice', 3: 'Eric'}
        color_map = {0: 'yellow', 1: 'green', 2: 'red', 3: 'white'}
        rows = []
        for i in range(4):
            house_num = i + 1
            n_val = model[name[i]].as_long()
            c_val = model[color[i]].as_long()
            rows.append([str(house_num), name_map[n_val], color_map[c_val]])
        solution = {
            "solution": {
                "header": ["House", "Name", "Color"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()