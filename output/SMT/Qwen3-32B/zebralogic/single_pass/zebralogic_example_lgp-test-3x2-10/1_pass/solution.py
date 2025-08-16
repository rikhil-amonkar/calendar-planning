from z3 import *
import json

solver = Solver()

# Define variables for each house's name and height
name1, name2, name3 = Ints('name1 name2 name3')
height1, height2, height3 = Ints('height1 height2 height3')

# Names are distinct and in range [0, 2]
solver.add(Distinct(name1, name2, name3))
solver.add(And([name1 >= 0, name1 <= 2, name2 >= 0, name2 <= 2, name3 >= 0, name3 <= 2]))

# Heights are distinct and in range [0, 2]
solver.add(Distinct(height1, height2, height3))
solver.add(And([height1 >= 0, height1 <= 2, height2 >= 0, height2 <= 2, height3 >= 0, height3 <= 2]))

# Clue 1: Eric (0) is not in the first house
solver.add(name1 != 0)

# Clue 4: Arnold (1) is not in the first house
solver.add(name1 != 1)

# Clue 3: Eric is very short (1)
solver.add(Implies(name1 == 0, height1 == 1))
solver.add(Implies(name2 == 0, height2 == 1))
solver.add(Implies(name3 == 0, height3 == 1))

# Clue 2: Very short (Eric) is to the left of short (0)
solver.add(Implies(name2 == 0, height3 == 0))
solver.add(Implies(name3 == 0, False))  # Eric cannot be in house 3

if solver.check() == sat:
    model = solver.model()
    # Extract values from the model
    n1 = model[name1].as_long()
    n2 = model[name2].as_long()
    n3 = model[name3].as_long()
    h1 = model[height1].as_long()
    h2 = model[height2].as_long()
    h3 = model[height3].as_long()

    # Mapping integers to names and heights
    name_map = {0: "Eric", 1: "Arnold", 2: "Peter"}
    height_map = {0: "short", 1: "very short", 2: "average"}

    # Construct the solution rows
    rows = [
        ["1", name_map[n1], height_map[h1]],
        ["2", name_map[n2], height_map[h2]],
        ["3", name_map[n3], height_map[h3]]
    ]

    solution = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }

    # Output as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")