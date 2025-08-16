from z3 import *
import json

# Define possible values for each category
nationalities = ["german", "swede", "norwegian", "brit", "dane"]
names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
animals = ["horse", "dog", "bird", "fish", "cat"]

# Create Z3 variables for each house (0-4)
n = [Int(f'n_{i}') for i in range(5)]  # Nationality
s = [Int(f's_{i}') for i in range(5)]  # Name
sm = [Int(f'sm_{i}') for i in range(5)]  # Smoothie
a = [Int(f'a_{i}') for i in range(5)]  # Animal

solver = Solver()

# Add constraints for distinct and range
for each in [n, s, sm, a]:
    solver.add(Distinct(each))
    for var in each:
        solver.add(And(var >= 0, var < 5))

# Add specific constraints based on clues
# Clue 11: Horse in house 3
solver.add(a[2] == 0)

# Clue 12: Norwegian is Alice
for i in range(5):
    solver.add(Implies(n[i] == 2, s[i] == 0))

# Clue 3: Dane is the horse keeper
for i in range(5):
    solver.add(Implies(n[i] == 4, a[i] == 0))
    solver.add(Implies(a[i] == 0, n[i] == 4))

# Clue 6: Eric is the cat lover
for i in range(5):
    solver.add(Implies(s[i] == 3, a[i] == 4))

# Clue 7: Bob is the bird keeper
for i in range(5):
    solver.add(Implies(s[i] == 2, a[i] == 2))

# Clue 9: Bird keeper is Watermelon smoothie lover
for i in range(5):
    solver.add(Implies(a[i] == 2, sm[i] == 3))

# Clue 10: Desert smoothie lover is the dog owner
for i in range(5):
    solver.add(Implies(sm[i] == 2, a[i] == 1))

# Clue 5: Dog owner is directly left of Lime smoothie
for i in range(4):
    solver.add(Implies(a[i] == 1, sm[i+1] == 0))

# Clue 1: Swedish person is directly left of dog owner
for i in range(4):
    solver.add(Implies(n[i] == 1, a[i+1] == 1))

# Clue 2: Two houses between dog owner and Brit
for x in range(5):
    for y in range(5):
        solver.add(Implies(And(a[x] == 1, n[y] == 3), Abs(x - y) == 3))

# Clue 4: Bird is to the right of cat
for i in range(5):
    for j in range(5):
        solver.add(Implies(And(a[i] == 2, a[j] == 4), i > j))

# Clue 8: Cherry smoothie lover is directly left of Peter
for i in range(4):
    solver.add(Implies(sm[i] == 4, s[i+1] == 1))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    rows = []
    for i in range(5):
        house_num = i + 1
        n_val = model[n[i]].as_long()
        s_val = model[s[i]].as_long()
        sm_val = model[sm[i]].as_long()
        a_val = model[a[i]].as_long()
        rows.append([
            str(house_num),
            names[s_val],
            smoothies[sm_val],
            animals[a_val],
            nationalities[n_val]
        ])
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")