import json
from z3 import *

solver = Solver()

# Variables for each house (0,1,2)
names = [Int('n_%d' % i) for i in range(3)]
smoothies = [Int('s_%d' % i) for i in range(3)]
flowers = [Int('f_%d' % i) for i in range(3)]
animals = [Int('a_%d' % i) for i in range(3)]
hobbies = [Int('h_%d' % i) for i in range(3)]

# Add distinct and range constraints
for var_list in [names, smoothies, flowers, animals, hobbies]:
    solver.add(Distinct(var_list))
    for var in var_list:
        solver.add(And(0 <= var, var < 3))

# Clue 1: Horse and photography are next to each other
for i in range(3):
    cond = animals[i] == 1  # horse
    if i == 0:
        neighbor_cond = Or(hobbies[1] == 0)  # photography in house 1
    elif i == 1:
        neighbor_cond = Or(hobbies[0] == 0, hobbies[2] == 0)
    else:  # i == 2
        neighbor_cond = Or(hobbies[1] == 0)
    solver.add(Implies(cond, neighbor_cond))

# Clue 2: Bird → cherry
for i in range(3):
    solver.add(Implies(animals[i] == 2, smoothies[i] == 0))

# Clue 3: Cooking → desert
for i in range(3):
    solver.add(Implies(hobbies[i] == 1, smoothies[i] == 2))

# Clue 4: Gardening → carnations
for i in range(3):
    solver.add(Implies(hobbies[i] == 2, flowers[i] == 0))

# Clue 5: Cooking directly left of Peter
solver.add(Implies(hobbies[0] == 1, names[1] == 1))  # if house 0 has cooking, house 1 is Peter
solver.add(Implies(hobbies[1] == 1, names[2] == 1))  # if house 1 has cooking, house 2 is Peter

# Clue 6: Daffodils → desert
for i in range(3):
    solver.add(Implies(flowers[i] == 2, smoothies[i] == 2))

# Also, cooking → daffodils (from clues 3 and 6)
for i in range(3):
    solver.add(Implies(hobbies[i] == 1, flowers[i] == 2))

# Clue 7: Watermelon → horse
for i in range(3):
    solver.add(Implies(smoothies[i] == 1, animals[i] == 1))

# Clue 8: Photography → Eric
for i in range(3):
    solver.add(Implies(hobbies[i] == 0, names[i] == 0))

# Solve
if solver.check() == sat:
    model = solver.model()
    # Mappings
    name_map = {0: 'Eric', 1: 'Peter', 2: 'Arnold'}
    smoothie_map = {0: 'cherry', 1: 'watermelon', 2: 'desert'}
    flower_map = {0: 'carnations', 1: 'lilies', 2: 'daffodils'}
    animal_map = {0: 'cat', 1: 'horse', 2: 'bird'}
    hobby_map = {0: 'photography', 1: 'cooking', 2: 'gardening'}
    
    rows = []
    for i in range(3):
        n = model.eval(names[i]).as_long()
        s = model.eval(smoothies[i]).as_long()
        f = model.eval(flowers[i]).as_long()
        a = model.eval(animals[i]).as_long()
        h = model.eval(hobbies[i]).as_long()
        rows.append([
            str(i + 1),
            name_map[n],
            smoothie_map[s],
            flower_map[f],
            animal_map[a],
            hobby_map[h]
        ])
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")