from z3 import *
import json

solver = Solver()

names = [Int(f'name_{i+1}') for i in range(6)]
haircolors = [Int(f'haircolor_{i+1}') for i in range(6)]
heights = [Int(f'height_{i+1}') for i in range(6)]

# All distinct
solver.add(Distinct(names))
solver.add(Distinct(haircolors))
solver.add(Distinct(heights))

# Each between 0 and 5
for var in names + haircolors + heights:
    solver.add(And(0 <= var, var < 6))

# Clue 2: Alice in house 4 (index 3)
solver.add(names[3] == 3)

# Clue 3: Arnold is short
for i in range(6):
    solver.add(Implies(names[i] == 4, heights[i] == 5))

# Clue 4: house 6 is tall (index 5)
solver.add(heights[5] == 3)

# Clue 5: house 4 not black
solver.add(haircolors[3] != 3)

# Clue 6: Eric has red
for i in range(6):
    solver.add(Implies(names[i] == 2, haircolors[i] == 4))

# Clue 8: Carol has blonde
for i in range(6):
    solver.add(And(
        Implies(haircolors[i] == 1, names[i] == 5),
        Implies(names[i] == 5, haircolors[i] == 1)
    ))

# Clue 1: Blonde directly left of Bob
clue1 = Or()
for i in range(5):
    clue1 = Or(clue1, And(haircolors[i] == 1, names[i+1] == 0))
solver.add(clue1)

# Clue 12: house 3 has gray
solver.add(haircolors[2] == 5)

# Clue 13: Blonde is very tall
for i in range(6):
    solver.add(Implies(haircolors[i] == 1, heights[i] == 0))

# Clue 9: one house between gray and red
solver.add(Or(haircolors[0] == 4, haircolors[4] == 4))

# Clue 10: house 5 is very short
solver.add(heights[4] == 2)

# Clue 11: Bob has brown
for i in range(6):
    solver.add(Implies(names[i] == 0, haircolors[i] == 2))

# Clue 7: super tall to the right of average
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(heights[i] == 1, heights[j] == 4), j > i))

if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(6):
        house_num = i + 1
        name_idx = model[names[i]].as_long()
        hair_idx = model[haircolors[i]].as_long()
        height_idx = model[heights[i]].as_long()
        name = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"][name_idx]
        hair = ["auburn", "blonde", "brown", "black", "red", "gray"][hair_idx]
        height = ["very tall", "average", "very short", "tall", "super tall", "short"][height_idx]
        solution.append([str(house_num), name, hair, height])
    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": solution
        }
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found")