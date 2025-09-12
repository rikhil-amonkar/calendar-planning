from z3 import *
import json

solver = Solver()

houses = 4

# Variables for each house (0-based index for 4 houses)
n = [Int(f'n_{i}') for i in range(houses)]  # Names
s = [Int(f's_{i}') for i in range(houses)]  # Smoothies
c = [Int(f'c_{i}') for i in range(houses)]  # Cigars
h = [Int(f'h_{i}') for i in range(houses)]  # Heights
p = [Int(f'p_{i}') for i in range(houses)]  # Phones

# Add distinct constraints for each attribute
for var in [n, s, c, h, p]:
    solver.add(Distinct(var[0], var[1], var[2], var[3]))

# Add clues
# Clue 1: Dragonfruit (s=0) → Eric (n=0)
for i in range(houses):
    solver.add(Implies(s[i] == 0, n[i] == 0))

# Clue 2: Dunhill (c=2) → Cherry (s=1)
for i in range(houses):
    solver.add(Implies(c[i] == 2, s[i] == 1))

# Clue 3: Samsung (p=1) directly left of iPhone (p=2)
solver.add(Or(
    And(p[0] == 1, p[1] == 2),
    And(p[1] == 1, p[2] == 2),
    And(p[2] == 1, p[3] == 2)
))

# Clue 4: Dunhill smoker (c=2) is to the right of very short (h=3)
for i in range(houses):
    for j in range(houses):
        solver.add(Implies(And(c[i] == 2, h[j] == 3), i > j))

# Clue 5: Watermelon (s=3) is to the right of Desert (s=2)
for i in range(houses):
    for j in range(houses):
        solver.add(Implies(And(s[i] == 3, s[j] == 2), i > j))

# Clue 6: Prince (c=3) → phone=3 (oneplus 9)
for i in range(houses):
    solver.add(Implies(c[i] == 3, p[i] == 3))

# Clue 7: Tall (h=0) is in house 3 (index 2)
solver.add(h[2] == 0)

# Clue 8: very short (h=3) → phone=2 (iphone 13)
for i in range(houses):
    solver.add(Implies(h[i] == 3, p[i] == 2))

# Clue 9: Blue Master (c=0) not in first house (house 0)
solver.add(c[0] != 0)

# Clue 10: Dunhill (c=2) → height=2 (short)
for i in range(houses):
    solver.add(Implies(c[i] == 2, h[i] == 2))

# Clue 11: Peter (n=1) not in house 3 (index 2)
solver.add(n[2] != 1)

# Clue 12: Arnold (n=2) → phone=0 (google pixel 6)
for i in range(houses):
    solver.add(Implies(n[i] == 2, p[i] == 0))

# Clue 13: Dragonfruit (s=0) → Pall Mall (c=1)
for i in range(houses):
    solver.add(Implies(s[i] == 0, c[i] == 1))

if solver.check() == sat:
    model = solver.model()
    # Mappings
    name_map = {0: 'Eric', 1: 'Peter', 2: 'Arnold', 3: 'Alice'}
    smoothie_map = {0: 'dragonfruit', 1: 'cherry', 2: 'desert', 3: 'watermelon'}
    cigar_map = {0: 'blue master', 1: 'pall mall', 2: 'dunhill', 3: 'prince'}
    height_map = {0: 'tall', 1: 'average', 2: 'short', 3: 'very short'}
    phone_map = {0: 'google pixel 6', 1: 'samsung galaxy s21', 2: 'iphone 13', 3: 'oneplus 9'}
    
    rows = []
    for i in range(4):
        house_num = i + 1
        n_val = model.eval(n[i]).as_long()
        s_val = model.eval(s[i]).as_long()
        c_val = model.eval(c[i]).as_long()
        h_val = model.eval(h[i]).as_long()
        p_val = model.eval(p[i]).as_long()
        row = [
            str(house_num),
            name_map[n_val],
            smoothie_map[s_val],
            cigar_map[c_val],
            height_map[h_val],
            phone_map[p_val]
        ]
        rows.append(row)
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")