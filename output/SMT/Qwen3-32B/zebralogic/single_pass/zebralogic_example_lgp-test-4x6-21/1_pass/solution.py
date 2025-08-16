from z3 import *
import json

solver = Solver()

# Define the variables for each house (1-4, indexes 0-3)
names = [Int('name_{}'.format(i+1)) for i in range(4)]
flowers = [Int('flower_{}'.format(i+1)) for i in range(4)]
hobbies = [Int('hobby_{}'.format(i+1)) for i in range(4)]
pets = [Int('pet_{}'.format(i+1)) for i in range(4)]
colors = [Int('color_{}'.format(i+1)) for i in range(4)]
housestyles = [Int('housestyle_{}'.format(i+1)) for i in range(4)]

# Add constraints that each attribute has distinct values and within 0-3
for var_list in [names, flowers, hobbies, pets, colors, housestyles]:
    solver.add(Distinct(var_list))
    for var in var_list:
        solver.add(And(0 <= var, var <= 3))

# Clue 6: Craftsman-style is in house 2 (index 1)
solver.add(housestyles[1] == 0)  # craftsman is 0

# Clue 1: Arnold (1) is in Craftsman (house 2, index 1)
solver.add(names[1] == 1)

# Clue 7: Eric (3) lives in Victorian (3)
for i in range(4):
    solver.add(Implies(names[i] == 3, housestyles[i] == 3))

# Clue 14: Eric has a cat (3)
for i in range(4):
    solver.add(Implies(names[i] == 3, pets[i] == 3))

# Clue 3: photography (0) → dog (0)
for i in range(4):
    solver.add(Implies(hobbies[i] == 0, pets[i] == 0))

# Clue 8: fish (1) → white (3)
for i in range(4):
    solver.add(Implies(pets[i] == 1, colors[i] == 3))

# Clue 10: white (3) → carnations (2)
for i in range(4):
    solver.add(Implies(colors[i] == 3, flowers[i] == 2))

# Clue 12: daffodils (1) → yellow (1)
for i in range(4):
    solver.add(Implies(flowers[i] == 1, colors[i] == 1))

# Clue 13: colonial (1) → red (0)
for i in range(4):
    solver.add(Implies(housestyles[i] == 1, colors[i] == 0))

# Clue 5: roses (0) → red (0)
for i in range(4):
    solver.add(Implies(flowers[i] == 0, colors[i] == 0))

# Clue 4: daffodils not in house 4 (index 3)
solver.add(flowers[3] != 1)

# Now handle positional constraints with helper variables

# Clue 2: roses lover is to the right of Peter
peter_house = Int('peter_house')
rose_house = Int('rose_house')
solver.add(Or([And(names[i] == 0, peter_house == i) for i in range(4)]))
solver.add(Or([And(flowers[i] == 0, rose_house == i) for i in range(4)]))
solver.add(rose_house > peter_house)

# Clue 9: cooking (2) is to the right of red color (0)
red_house = Int('red_house')
cooking_house = Int('cooking_house')
solver.add(Or([And(colors[i] == 0, red_house == i) for i in range(4)]))
solver.add(Or([And(hobbies[i] == 2, cooking_house == i) for i in range(4)]))
solver.add(cooking_house > red_house)

# Clue 11: white (3) is to the right of gardening (3)
white_house = Int('white_house')
gardening_house = Int('gardening_house')
solver.add(Or([And(colors[i] == 3, white_house == i) for i in range(4)]))
solver.add(Or([And(hobbies[i] == 3, gardening_house == i) for i in range(4)]))
solver.add(white_house > gardening_house)

# Now check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Now extract the values for each house and attribute
    # First, create mappings from integer to string
    name_map = {0: 'Peter', 1: 'Arnold', 2: 'Alice', 3: 'Eric'}
    flower_map = {0: 'roses', 1: 'daffodils', 2: 'carnations', 3: 'lilies'}
    hobby_map = {0: 'photography', 1: 'painting', 2: 'cooking', 3: 'gardening'}
    pet_map = {0: 'dog', 1: 'fish', 2: 'bird', 3: 'cat'}
    color_map = {0: 'red', 1: 'yellow', 2: 'green', 3: 'white'}
    housestyle_map = {0: 'craftsman', 1: 'colonial', 2: 'ranch', 3: 'victorian'}

    rows = []
    for i in range(4):  # for each house 1-4 (indexes 0-3)
        house_num = i + 1
        name_val = model[names[i]].as_long()
        flower_val = model[flowers[i]].as_long()
        hobby_val = model[hobbies[i]].as_long()
        pet_val = model[pets[i]].as_long()
        color_val = model[colors[i]].as_long()
        housestyle_val = model[housestyles[i]].as_long()

        row = [
            str(house_num),
            name_map[name_val],
            flower_map[flower_val],
            hobby_map[hobby_val],
            pet_map[pet_val],
            color_map[color_val],
            housestyle_map[housestyle_val]
        ]
        rows.append(row)

    # Now create the JSON structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
            "rows": rows
        }
    }

    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")