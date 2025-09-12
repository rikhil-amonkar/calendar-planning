from z3 import *
import json

solver = Solver()

# Define variables for each house (1, 2, 3) and each attribute
name1, name2, name3 = Ints('name1 name2 name3')
bg1, bg2, bg3 = Ints('bg1 bg2 bg3')  # BookGenre
sm1, sm2, sm3 = Ints('sm1 sm2 sm3')  # Smoothie
bd1, bd2, bd3 = Ints('bd1 bd2 bd3')  # Birthday
ht1, ht2, ht3 = Ints('ht1 ht2 ht3')  # Height

# Add constraints for distinctness and valid ranges for each attribute
for var in [name1, name2, name3]:
    solver.add(And(0 <= var, var <= 2))
solver.add(Distinct(name1, name2, name3))

for var in [bg1, bg2, bg3]:
    solver.add(And(0 <= var, var <= 2))
solver.add(Distinct(bg1, bg2, bg3))

for var in [sm1, sm2, sm3]:
    solver.add(And(0 <= var, var <= 2))
solver.add(Distinct(sm1, sm2, sm3))

for var in [bd1, bd2, bd3]:
    solver.add(And(0 <= var, var <= 2))
solver.add(Distinct(bd1, bd2, bd3))

for var in [ht1, ht2, ht3]:
    solver.add(And(0 <= var, var <= 2))
solver.add(Distinct(ht1, ht2, ht3))

# Add constraints based on clues
# Clue 1: Cherry smoothie not in second house
solver.add(sm2 != 2)

# Clue 2: Arnold loves mystery books
solver.add(Or(
    And(name1 == 1, bg1 == 1),
    And(name2 == 1, bg2 == 1),
    And(name3 == 1, bg3 == 1)
))

# Clue 3: Birthday in January not in first house
solver.add(bd1 != 1)

# Clue 4: Very short person loves romance books
solver.add(Implies(ht1 == 1, bg1 == 2))
solver.add(Implies(ht2 == 1, bg2 == 2))
solver.add(Implies(ht3 == 1, bg3 == 2))

# Clue 5: Mystery book lover's birthday is September
solver.add(Implies(bg1 == 1, bd1 == 2))
solver.add(Implies(bg2 == 1, bd2 == 2))
solver.add(Implies(bg3 == 1, bd3 == 2))

# Clue 6: Average height person loves desert smoothie
solver.add(Implies(ht1 == 0, sm1 == 1))
solver.add(Implies(ht2 == 0, sm2 == 1))
solver.add(Implies(ht3 == 0, sm3 == 1))

# Clue 7: Eric is in the first house
solver.add(name1 == 2)

# Clue 8: Watermelon lover is short
solver.add(Implies(sm1 == 0, ht1 == 2))
solver.add(Implies(sm2 == 0, ht2 == 2))
solver.add(Implies(sm3 == 0, ht3 == 2))

# Clue 9: Watermelon lover is Eric (in house 1)
solver.add(sm1 == 0)

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    
    # Mapping from integer values to strings
    name_map = {0: 'Peter', 1: 'Arnold', 2: 'Eric'}
    bookgenre_map = {0: 'science fiction', 1: 'mystery', 2: 'romance'}
    smoothie_map = {0: 'watermelon', 1: 'desert', 2: 'cherry'}
    birthday_map = {0: 'april', 1: 'jan', 2: 'sept'}
    height_map = {0: 'average', 1: 'very short', 2: 'short'}
    
    # Extract solution data
    rows = []
    for i in range(3):
        house_num = i + 1
        name_val = model.eval([name1, name2, name3][i]).as_long()
        bg_val = model.eval([bg1, bg2, bg3][i]).as_long()
        sm_val = model.eval([sm1, sm2, sm3][i]).as_long()
        bd_val = model.eval([bd1, bd2, bd3][i]).as_long()
        ht_val = model.eval([ht1, ht2, ht3][i]).as_long()
        
        rows.append([
            str(house_num),
            name_map[name_val],
            bookgenre_map[bg_val],
            smoothie_map[sm_val],
            birthday_map[bd_val],
            height_map[ht_val]
        ])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")