import json
from z3 import *

def main():
    solver = Solver()

    houses = range(1, 6)  # 1-based
    name = [Int(f'name_{i}') for i in houses]
    height = [Int(f'height_{i}') for i in houses]
    mother = [Int(f'mother_{i}') for i in houses]
    hair_color = [Int(f'hair_color_{i}') for i in houses]

    # All attributes are permutations (distinct)
    for attr in [name, height, mother, hair_color]:
        solver.add(Distinct(attr))

    # Clue 8: Bob is in house 5 (index 4)
    solver.add(name[4] == 2)  # Bob is index 2

    # Clue 14: mother[3] is Kailyn (index 1)
    solver.add(mother[2] == 1)  # house 3 is index 2

    # Clue 10 and 14 imply height[4] (house 4, index 3) is short (1)
    solver.add(height[3] == 1)

    # Clue 2: average (3) in house 1 (index 0)
    solver.add(height[0] == 3)

    # Clue 5: Eric (3) has black hair (1)
    for i in range(5):
        solver.add(If(name[i] == 3, hair_color[i] == 1, True))

    # Clue 9: red hair (3) is Peter (1)
    for i in range(5):
        solver.add(If(hair_color[i] == 3, name[i] == 1, True))

    # Clue 11: Arnold (4) has brown hair (4)
    for i in range(5):
        solver.add(If(name[i] == 4, hair_color[i] == 4, True))

    # Clue 4: house 5's hair color is not black (1)
    solver.add(hair_color[4] != 1)

    # Clue 1: tall (2) has mother Holly (3)
    for i in range(5):
        solver.add(If(height[i] == 2, mother[i] == 3, True))

    # Clue 6: very short (0) has mother Penny (2)
    for i in range(5):
        solver.add(If(height[i] == 0, mother[i] == 2, True))

    # Clue 7: Eric and gray hair (2) are adjacent
    for i in range(5):
        if i == 0:
            solver.add(If(name[i] == 3, hair_color[i+1] == 2, True))
        elif i == 4:
            solver.add(If(name[i] == 3, hair_color[i-1] == 2, True))
        else:
            solver.add(If(name[i] == 3, Or(hair_color[i-1] == 2, hair_color[i+1] == 2), True))

    # Clue 3: gray hair directly left of mother Janelle (0)
    solver.add(Or(
        And(hair_color[0] == 2, mother[1] == 0),
        And(hair_color[1] == 2, mother[2] == 0),
        And(hair_color[2] == 2, mother[3] == 0),
        And(hair_color[3] == 2, mother[4] == 0)
    ))

    # Clue 12: brown hair (4) is left of mother Janelle (0)
    brown_house = Int('brown_house')
    janelle_house = Int('janelle_house')
    for i in range(5):
        solver.add(Implies(hair_color[i] == 4, brown_house == i))
    solver.add(And(hair_color[brown_house] == 4, 0 <= brown_house, brown_house <= 4))
    for i in range(5):
        solver.add(Implies(mother[i] == 0, janelle_house == i))
    solver.add(And(mother[janelle_house] == 0, 0 <= janelle_house, janelle_house <= 4))
    solver.add(brown_house < janelle_house)

    # Clue 13: very short (0) is adjacent to mother Aniya (4)
    for i in range(5):
        if i == 0:
            solver.add(If(height[i] == 0, mother[i+1] == 4, True))
        elif i == 4:
            solver.add(If(height[i] == 0, mother[i-1] == 4, True))
        else:
            solver.add(If(height[i] == 0, Or(mother[i-1] == 4, mother[i+1] == 4), True))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        # Prepare the solution
        name_list = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
        height_list = ['very short', 'short', 'tall', 'average', 'very tall']
        mother_list = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
        hair_color_list = ['blonde', 'black', 'gray', 'red', 'brown']

        rows = []
        for i in range(1, 6):
            idx = i - 1
            n = model[name[idx]].as_long()
            h = model[height[idx]].as_long()
            m = model[mother[idx]].as_long()
            hc = model[hair_color[idx]].as_long()
            rows.append([
                str(i),
                name_list[n],
                height_list[h],
                mother_list[m],
                hair_color_list[hc]
            ])

        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                "rows": rows
            }
        }

        print(json.dumps(solution))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()