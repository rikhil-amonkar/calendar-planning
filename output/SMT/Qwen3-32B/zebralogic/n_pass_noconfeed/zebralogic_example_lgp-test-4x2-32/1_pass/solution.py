import json
from z3 import *

s = Solver()

names = [Int(f'names_{i}') for i in range(4)]
pets = [Int(f'pets_{i}') for i in range(4)]

# Add constraints for names to be permutation of 0-3
for i in range(4):
    s.add(And(0 <= names[i], names[i] <= 3))
s.add(Distinct(names))

# Same for pets
for i in range(4):
    s.add(And(0 <= pets[i], pets[i] <= 3))
s.add(Distinct(pets))

# Clue 2: Eric not in first house (names[0] != 2)
s.add(names[0] != 2)

# Clue 5: Alice not in first house (names[0] != 3)
s.add(names[0] != 3)

# Clue 3: Eric has bird
for h in range(4):
    s.add(Implies(names[h] == 2, pets[h] == 0))

# Clue 6: Arnold has fish
for h in range(4):
    s.add(Implies(names[h] == 1, pets[h] == 1))

# Clue 4: Fish and Peter are two apart
for h in range(4):
    target_p = (h + 2) % 4
    s.add(Implies(names[h] == 1, names[target_p] == 0))

# Clue 1: Dog is to the right of Alice
for i in range(4):
    for j in range(4):
        s.add(Implies(And(names[i] == 3, pets[j] == 2), j > i))

if s.check() == sat:
    model = s.model()
    rows = []
    name_map = {0: 'Peter', 1: 'Arnold', 2: 'Eric', 3: 'Alice'}
    pet_map = {0: 'bird', 1: 'fish', 2: 'dog', 3: 'cat'}
    for i in range(4):
        house_num = i + 1
        n = model.eval(names[i]).as_long()
        p = model.eval(pets[i]).as_long()
        rows.append([str(house_num), name_map[n], pet_map[p]])
    solution = {
        "solution": {
            "header": ["House", "Name", "Pet"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")