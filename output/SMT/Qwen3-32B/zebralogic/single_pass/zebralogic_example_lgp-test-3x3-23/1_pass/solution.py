from z3 import *
import json

def main():
    solver = Solver()

    # Variables for each house (0, 1, 2)
    name = [Int(f'name_{i}') for i in range(3)]
    occupation = [Int(f'occupation_{i}') for i in range(3)]
    hobby = [Int(f'hobby_{i}') for i in range(3)]

    # All variables are 0-2 and distinct
    for var_list in [name, occupation, hobby]:
        for i in range(3):
            solver.add(var_list[i] >= 0, var_list[i] <= 2)
        solver.add(Distinct(*var_list))

    # Clue 5: Engineer is Peter
    for i in range(3):
        solver.add(If(occupation[i] == 2, name[i] == 0, True))

    # Clue 4: Teacher's hobby is photography
    for i in range(3):
        solver.add(If(occupation[i] == 1, hobby[i] == 1, True))

    # Clue 3: Doctor is to the right of gardening
    d = Int('d')
    g = Int('g')
    solver.add(Or(d == 0, d == 1, d == 2))
    solver.add(Or(
        And(occupation[0] == 0, d == 0),
        And(occupation[1] == 0, d == 1),
        And(occupation[2] == 0, d == 2)
    ))
    solver.add(Or(
        And(hobby[0] == 2, g == 0),
        And(hobby[1] == 2, g == 1),
        And(hobby[2] == 2, g == 2)
    ))
    solver.add(d > g)

    # Clue 2: Cooking directly left of teacher
    solver.add(Or(
        And(hobby[0] == 0, occupation[1] == 1),
        And(hobby[1] == 0, occupation[2] == 1)
    ))

    # Clue 1: Doctor and Eric are adjacent
    e = Int('e')
    solver.add(Or(
        And(name[0] == 2, e == 0),
        And(name[1] == 2, e == 1),
        And(name[2] == 2, e == 2)
    ))
    solver.add(Abs(d - e) == 1)

    if solver.check() == sat:
        model = solver.model()
        # Map the integers to strings
        name_map = {0: 'Peter', 1: 'Arnold', 2: 'Eric'}
        occupation_map = {0: 'doctor', 1: 'teacher', 2: 'engineer'}
        hobby_map = {0: 'cooking', 1: 'photography', 2: 'gardening'}
        rows = []
        for i in range(3):
            house_num = i + 1
            n = model[name[i]].as_long()
            o = model[occupation[i]].as_long()
            h = model[hobby[i]].as_long()
            rows.append([str(house_num), name_map[n], occupation_map[o], hobby_map[h]])
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()