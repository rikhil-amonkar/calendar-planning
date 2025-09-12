from z3 import *
import json

solver = Solver()

# Variables for each house (0 to 3 for houses 1-4)
name = [Int(f'name_{i}') for i in range(4)]
flower = [Int(f'flower_{i}') for i in range(4)]
height = [Int(f'height_{i}') for i in range(4)]
mother = [Int(f'mother_{i}') for i in range(4)]
occupation = [Int(f'occupation_{i}') for i in range(4)]
sport = [Int(f'sport_{i}') for i in range(4)]

# Add constraints for uniqueness and domain
for var_list in [name, flower, height, mother, occupation, sport]:
    solver.add(Distinct(var_list))
    for var in var_list:
        solver.add(And(0 <= var, var < 4))

# Add clues
# Clue 6: Teacher in first house (index 0)
solver.add(occupation[0] == 2)  # teacher is 2

# Clue 11: Peter (0) is doctor (1)
for i in range(4):
    solver.add(Or(name[i] != 0, occupation[i] == 1))

# Clue 3: Arnold (1) is tall (2)
for i in range(4):
    solver.add(Or(name[i] != 1, height[i] == 2))

# Clue 13: Arnold (1) loves lilies (3)
for i in range(4):
    solver.add(Or(name[i] != 1, flower[i] == 3))

# Clue 12: Alice (3) has mother Aniya (3)
for i in range(4):
    solver.add(Or(name[i] != 3, mother[i] == 3))

# Clue 2: roses (2) → Eric (2)
for i in range(4):
    solver.add(Or(flower[i] != 2, name[i] == 2))

# Clue 1: swimming (0) → roses (2)
for i in range(4):
    solver.add(Or(sport[i] != 0, flower[i] == 2))

# Clue 5: soccer (3) → short (1)
for i in range(4):
    solver.add(Or(sport[i] != 3, height[i] == 1))

# Clue 7: mother Janelle (0) → carnations (1)
for i in range(4):
    solver.add(Or(mother[i] != 0, flower[i] == 1))

# Clue 8: basketball (1) → average (3)
for i in range(4):
    solver.add(Or(sport[i] != 1, height[i] == 3))

# Clue 9: Arnold not in third house (index 2)
solver.add(name[2] != 1)

# Clue 4: daffodils (0) to the right of engineer (0)
pos_daffodils = Int('pos_daffodils')
pos_engineer = Int('pos_engineer')
for i in range(4):
    solver.add(Implies(flower[i] == 0, pos_daffodils == i))
    solver.add(Implies(occupation[i] == 0, pos_engineer == i))
solver.add(Or([pos_daffodils == i for i in range(4)]))
solver.add(Or([pos_engineer == i for i in range(4)]))
solver.add(pos_daffodils > pos_engineer)

# Clue 10: mother Holly (2) to the right of average height (3)
pos_mother_holly = Int('pos_mother_holly')
pos_avg_height = Int('pos_avg_height')
for i in range(4):
    solver.add(Implies(mother[i] == 2, pos_mother_holly == i))
    solver.add(Implies(height[i] == 3, pos_avg_height == i))
solver.add(Or([pos_mother_holly == i for i in range(4)]))
solver.add(Or([pos_avg_height == i for i in range(4)]))
solver.add(pos_mother_holly > pos_avg_height)

# Now check
if solver.check() == sat:
    model = solver.model()
    # Mappings
    name_map = {0: 'Peter', 1: 'Arnold', 2: 'Eric', 3: 'Alice'}
    flower_map = {0: 'daffodils', 1: 'carnations', 2: 'roses', 3: 'lilies'}
    height_map = {0: 'very short', 1: 'short', 2: 'tall', 3: 'average'}
    mother_map = {0: 'Janelle', 1: 'Kailyn', 2: 'Holly', 3: 'Aniya'}
    occupation_map = {0: 'engineer', 1: 'doctor', 2: 'teacher', 3: 'artist'}
    sport_map = {0: 'swimming', 1: 'basketball', 2: 'tennis', 3: 'soccer'}
    
    rows = []
    for i in range(4):
        house_num = i + 1
        n = model.eval(name[i]).as_long()
        f = model.eval(flower[i]).as_long()
        h = model.eval(height[i]).as_long()
        m = model.eval(mother[i]).as_long()
        o = model.eval(occupation[i]).as_long()
        s = model.eval(sport[i]).as_long()
        row = [
            str(house_num),
            name_map[n],
            flower_map[f],
            height_map[h],
            mother_map[m],
            occupation_map[o],
            sport_map[s]
        ]
        rows.append(row)
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")