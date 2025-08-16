from z3 import *
import json

def main():
    solver = Solver()

    names = [Int(f'name_{i}') for i in range(4)]
    hair_colors = [Int(f'hair_color_{i}') for i in range(4)]

    for i in range(4):
        solver.add(And(0 <= names[i], names[i] <= 3))
        solver.add(And(0 <= hair_colors[i], hair_colors[i] <= 3))

    solver.add(Distinct(names))
    solver.add(Distinct(hair_colors))

    # Clue 5: Alice is in the first house
    solver.add(names[0] == 0)  # Alice is 0

    # Clue 2: Alice and Arnold are next to each other (Arnold must be in house 2)
    solver.add(names[1] == 1)  # Arnold is 1

    # Clue 4: Black hair is not in the first house
    solver.add(hair_colors[0] != 0)

    # Clue 3: Eric has brown hair
    for i in range(4):
        solver.add(Implies(names[i] == 3, hair_colors[i] == 2))  # Eric is 3, brown is 2

    # Clue 1: Eric is directly left of the person with blonde hair
    solver.add(Or(
        And(names[0] == 3, hair_colors[1] == 1),
        And(names[1] == 3, hair_colors[2] == 1),
        And(names[2] == 3, hair_colors[3] == 1)
    ))

    if solver.check() == sat:
        model = solver.model()
        house_names = [model.eval(names[i]).as_long() for i in range(4)]
        house_hair_colors = [model.eval(hair_colors[i]).as_long() for i in range(4)]

        name_map = {0: 'Alice', 1: 'Arnold', 2: 'Peter', 3: 'Eric'}
        hair_color_map = {0: 'black', 1: 'blonde', 2: 'brown', 3: 'red'}

        rows = []
        for i in range(4):
            house_num = str(i + 1)
            name = name_map[house_names[i]]
            hair_color = hair_color_map[house_hair_colors[i]]
            rows.append([house_num, name, hair_color])

        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor"],
                "rows": rows
            }
        }

        print(json.dumps(solution))

if __name__ == "__main__":
    main()