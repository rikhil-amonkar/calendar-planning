import z3
import json

solver = z3.Solver()

# Define variables for each house (0-5)
name = [z3.Int(f'name_{i}') for i in range(6)]
child = [z3.Int(f'child_{i}') for i in range(6)]
smoothie = [z3.Int(f'smoothie_{i}') for i in range(6)]

# Each array must be a permutation (distinct and 0-5)
for arr in [name, child, smoothie]:
    solver.add(z3.Distinct(arr))
    for i in range(6):
        solver.add(z3.And(0 <= arr[i], arr[i] < 6))

# Clue 1: Fred and Desert next to each other
pos_fred = z3.Int('pos_fred')
for i in range(6):
    solver.add(z3.Implies(child[i] == 4, pos_fred == i))
pos_desert = z3.Int('pos_desert')
for i in range(6):
    solver.add(z3.Implies(smoothie[i] == 0, pos_desert == i))
solver.add(z3.Abs(pos_fred - pos_desert) == 1)

# Clue 2: Blueberry left of Fred's parent
pos_blueberry = z3.Int('pos_blueberry')
for i in range(6):
    solver.add(z3.Implies(smoothie[i] == 3, pos_blueberry == i))
solver.add(pos_blueberry < pos_fred)

# Clue 3: Alice not in house 5 (index 4)
solver.add(name[4] != 3)

# Clue 4: Samantha's parent not in house 2 (index 1)
pos_samantha = z3.Int('pos_samantha')
for i in range(6):
    solver.add(z3.Implies(child[i] == 5, pos_samantha == i))
solver.add(pos_samantha != 1)

# Clue 5: Watermelon right of Cherry
pos_watermelon = z3.Int('pos_watermelon')
pos_cherry = z3.Int('pos_cherry')
for i in range(6):
    solver.add(z3.Implies(smoothie[i] == 2, pos_watermelon == i))
    solver.add(z3.Implies(smoothie[i] == 1, pos_cherry == i))
solver.add(pos_watermelon > pos_cherry)

# Clue 6: Alice (name) is parent of Alice (child)
for i in range(6):
    solver.add(z3.Implies(name[i] == 3, child[i] == 0))

# Clue 7: Alice's smoothie is Watermelon
for i in range(6):
    solver.add(z3.Implies(name[i] == 3, smoothie[i] == 2))

# Clue 8: Peter (index 1) is right of Samantha's parent
pos_peter = z3.Int('pos_peter')
for i in range(6):
    solver.add(z3.Implies(name[i] == 1, pos_peter == i))
solver.add(pos_peter > pos_samantha)

# Clue 9: Arnold not in house 2 (index 1)
solver.add(name[1] != 0)

# Clue 10: Bob is parent of Timothy
for i in range(6):
    solver.add(z3.Implies(name[i] == 4, child[i] == 1))

# Clue 11: Arnold directly left of Carol
solver.add(z3.Or([z3.And(name[i] == 0, name[i+1] == 2) for i in range(5)]))

# Clue 12: Cherry directly left of Samantha's parent
solver.add(pos_samantha == pos_cherry + 1)

# Clue 13: Meredith's parent in house 6 (index 5)
solver.add(child[5] == 3)

# Clue 14: Dragonfruit lover is Meredith's parent (house 5)
solver.add(smoothie[5] == 5)

if solver.check() == z3.sat:
    model = solver.model()
    names_list = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    children_list = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothie_list = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]
    
    rows = []
    for i in range(6):
        n = model.eval(name[i]).as_long()
        c = model.eval(child[i]).as_long()
        s = model.eval(smoothie[i]).as_long()
        house_num = i + 1
        rows.append([
            str(house_num),
            names_list[n],
            children_list[c],
            smoothie_list[s]
        ])
    solution = {
        "solution": {
            "header": ["House", "Name", "Children", "Smoothie"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")