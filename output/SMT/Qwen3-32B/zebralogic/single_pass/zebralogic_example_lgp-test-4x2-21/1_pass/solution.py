import z3
import json

solver = z3.Solver()

names = [z3.Int(f'name_{i}') for i in range(4)]
styles = [z3.Int(f'style_{i}') for i in range(4)]

# All names are distinct and between 0-3
solver.add(z3.Distinct(names))
for n in names:
    solver.add(z3.And(n >= 0, n <= 3))

# All styles are distinct and between 0-3
solver.add(z3.Distinct(styles))
for s in styles:
    solver.add(z3.And(s >= 0, s <= 3))

# Clue 1: Alice is in the second house (index 1)
solver.add(names[1] == 2)

# Clue 5: Alice's house is Craftsman (index 1)
solver.add(styles[1] == 0)

# Clue 2: Victorian directly left of Peter
clue2 = z3.Or(
    z3.And(styles[0] == 3, names[1] == 3),
    z3.And(styles[1] == 3, names[2] == 3),
    z3.And(styles[2] == 3, names[3] == 3)
)
solver.add(clue2)

# Clue 3: Peter is to the right of ranch
clue3a = z3.Implies(styles[0] == 2, z3.Or(names[1] == 3, names[2] == 3, names[3] == 3))
clue3b = z3.Implies(styles[1] == 2, z3.Or(names[2] == 3, names[3] == 3))
clue3c = z3.Implies(styles[2] == 2, names[3] == 3)
clue3d = (styles[3] != 2)
solver.add(clue3a, clue3b, clue3c, clue3d)

# Clue 4: Arnold is to the right of Craftsman (house 2, index 1)
solver.add(z3.Not(names[0] == 1))
solver.add(z3.Not(names[1] == 1))

if solver.check() == z3.sat:
    model = solver.model()
    names_vals = [model.eval(n).as_long() for n in names]
    styles_vals = [model.eval(s).as_long() for s in styles]
    
    name_map = {0: 'Eric', 1: 'Arnold', 2: 'Alice', 3: 'Peter'}
    style_map = {0: 'craftsman', 1: 'colonial', 2: 'ranch', 3: 'victorian'}
    
    rows = []
    for i in range(4):
        house_num = i + 1
        name = name_map[names_vals[i]]
        style = style_map[styles_vals[i]]
        rows.append([str(house_num), name, style])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")