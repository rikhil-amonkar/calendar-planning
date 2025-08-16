from z3 import *
import json

# Define the possible values as lists for mapping later
names_list = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
drinks_list = ["milk", "root beer", "coffee", "tea", "water"]
colors_list = ["blue", "green", "white", "yellow", "red"]
flowers_list = ["daffodils", "roses", "lilies", "tulips", "carnations"]
hobbies_list = ["painting", "cooking", "photography", "gardening", "knitting"]

solver = Solver()

# Create variables for each house (0-4)
name = [Int(f'name_{i}') for i in range(5)]
drink = [Int(f'drink_{i}') for i in range(5)]
color = [Int(f'color_{i}') for i in range(5)]
flower = [Int(f'flower_{i}') for i in range(5)]
hobby = [Int(f'hobby_{i}') for i in range(5)]

# Add constraints for each attribute to be a permutation (distinct and 0-4)
for attr in [name, drink, color, flower, hobby]:
    solver.add(Distinct(attr))
    for v in attr:
        solver.add(And(0 <= v, v <= 4))

# Clue 1: Alice not in house 4 (index 3)
solver.add(name[3] != 3)  # Alice is index 3 in names_list

# Clue 2: root beer (1) → gardening (3)
for i in range(5):
    solver.add(Implies(drink[i] == 1, hobby[i] == 3))

# Clue 3: green (1) → coffee (2)
for i in range(5):
    solver.add(Implies(color[i] == 1, drink[i] == 2))

# Clue 4: green (1) → lilies (2)
for i in range(5):
    solver.add(Implies(color[i] == 1, flower[i] == 2))

# Clue 5: blue (0) is to the right of daffodils (0)
i_blue = Int('i_blue')
i_daffodils = Int('i_daffodils')
for i in range(5):
    solver.add(Implies(color[i] == 0, i == i_blue))
    solver.add(Implies(i == i_blue, color[i] == 0))
    solver.add(Implies(flower[i] == 0, i == i_daffodils))
    solver.add(Implies(i == i_daffodils, flower[i] == 0))
solver.add(i_blue > i_daffodils)

# Clue 6: cooking (1) → blue (0)
for i in range(5):
    solver.add(Implies(hobby[i] == 1, color[i] == 0))

# Clue 7: Eric (4) directly left of tea (3)
solver.add(Or(
    And(name[0] == 4, drink[1] == 3),
    And(name[1] == 4, drink[2] == 3),
    And(name[2] == 4, drink[3] == 3),
    And(name[3] == 4, drink[4] == 3)
))

# Clue 8: Peter (2) drinks water (4)
for i in range(5):
    solver.add(Implies(name[i] == 2, drink[i] == 4))

# Clue 9: Arnold (1) → photography (2)
for i in range(5):
    solver.add(Implies(name[i] == 1, hobby[i] == 2))

# Clue 10: white (2) → roses (1)
for i in range(5):
    solver.add(Implies(color[i] == 2, flower[i] == 1))

# Clue 11: carnations (4) and red (4) with one house between
i_carnations = Int('i_carnations')
i_red = Int('i_red')
for i in range(5):
    solver.add(Implies(flower[i] == 4, i == i_carnations))
    solver.add(Implies(i == i_carnations, flower[i] == 4))
    solver.add(Implies(color[i] == 4, i == i_red))
    solver.add(Implies(i == i_red, color[i] == 4))
solver.add(Abs(i_carnations - i_red) == 2)

# Clue 12: cooking (1) left of painting (0)
i_cooking = Int('i_cooking')
i_painting = Int('i_painting')
for i in range(5):
    solver.add(Implies(hobby[i] == 1, i == i_cooking))
    solver.add(Implies(i == i_cooking, hobby[i] == 1))
    solver.add(Implies(hobby[i] == 0, i == i_painting))
    solver.add(Implies(i == i_painting, hobby[i] == 0))
solver.add(i_cooking < i_painting)

# Clue 13: water (4) in house 3 (index 2)
solver.add(drink[2] == 4)
# Also, Peter is in house 3 (from clue 8)
solver.add(name[2] == 2)

# Clue 14: carnations (4) → root beer (1)
for i in range(5):
    solver.add(Implies(flower[i] == 4, drink[i] == 1))

# Clue 15: white (2) in house 2 (index 1)
solver.add(color[1] == 2)

# Now, check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Now extract the values for each house
    solution = []
    for i in range(5):
        house_num = i + 1
        name_val = names_list[model[name[i]].as_long()]
        drink_val = drinks_list[model[drink[i]].as_long()]
        color_val = colors_list[model[color[i]].as_long()]
        flower_val = flowers_list[model[flower[i]].as_long()]
        hobby_val = hobbies_list[model[hobby[i]].as_long()]
        solution.append([str(house_num), name_val, drink_val, color_val, flower_val, hobby_val])
    # Output the JSON
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": solution
        }
    }, indent=2))
else:
    print("No solution found.")