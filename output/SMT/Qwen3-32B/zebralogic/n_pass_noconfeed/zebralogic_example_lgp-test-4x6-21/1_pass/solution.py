import json
from z3 import *

# Define the attributes and their possible values
names = ["Peter", "Arnold", "Alice", "Eric"]
flowers = ["roses", "daffodils", "carnations", "lilies"]
hobbies = ["photography", "painting", "cooking", "gardening"]
pets = ["dog", "fish", "bird", "cat"]
colors = ["red", "yellow", "green", "white"]
house_styles = ["craftsman", "colonial", "ranch", "victorian"]

# Create mappings from string to index
name_to_idx = {name: i for i, name in enumerate(names)}
flower_to_idx = {f: i for i, f in enumerate(flowers)}
hobby_to_idx = {h: i for i, h in enumerate(hobbies)}
pet_to_idx = {p: i for i, p in enumerate(pets)}
color_to_idx = {c: i for i, c in enumerate(colors)}
style_to_idx = {s: i for i, s in enumerate(house_styles)}

# Reverse mappings for output
idx_to_name = {v: k for k, v in name_to_idx.items()}
idx_to_flower = {v: k for k, v in flower_to_idx.items()}
idx_to_hobby = {v: k for k, v in hobby_to_idx.items()}
idx_to_pet = {v: k for k, v in pet_to_idx.items()}
idx_to_color = {v: k for k, v in color_to_idx.items()}
idx_to_style = {v: k for k, v in style_to_idx.items()}

# Create variables for each house's attributes
name_vars = [Int(f'name_{i}') for i in range(4)]
flower_vars = [Int(f'flower_{i}') for i in range(4)]
hobby_vars = [Int(f'hobby_{i}') for i in range(4)]
pet_vars = [Int(f'pet_{i}') for i in range(4)]
color_vars = [Int(f'color_{i}') for i in range(4)]
style_vars = [Int(f'style_{i}') for i in range(4)]

solver = Solver()

# Add constraints that all variables are in 0-3 and distinct per attribute
for vars in [name_vars, flower_vars, hobby_vars, pet_vars, color_vars, style_vars]:
    for v in vars:
        solver.add(And(0 <= v, v < 4))
    solver.add(Distinct(vars))

# Add clue constraints
# Clue 1 and 6: Craftsman is Arnold in house 2 (index 1)
solver.add(style_vars[1] == style_to_idx['craftsman'])  # clue 6
solver.add(name_vars[1] == name_to_idx['Arnold'])  # clue 1

# Clue 2: Rose lover is to the right of Peter
roses_idx = flower_to_idx['roses']
peter_idx = name_to_idx['Peter']
solver.add(Or([And(flower_vars[i] == roses_idx, name_vars[j] == peter_idx, i > j) for i in range(4) for j in range(4)]))

# Clue 3: Photography is dog
for i in range(4):
    solver.add(Implies(hobby_vars[i] == hobby_to_idx['photography'], pet_vars[i] == pet_to_idx['dog']))

# Clue 4: Daffodils not in fourth house
daffodils_idx = flower_to_idx['daffodils']
solver.add(flower_vars[3] != daffodils_idx)

# Clue 5: Rose lover's color is red
red_idx = color_to_idx['red']
for i in range(4):
    solver.add(Implies(flower_vars[i] == roses_idx, color_vars[i] == red_idx))

# Clue 7: Eric in Victorian
eric_idx = name_to_idx['Eric']
victorian_idx = style_to_idx['victorian']
for i in range(4):
    solver.add(Implies(name_vars[i] == eric_idx, style_vars[i] == victorian_idx))

# Clue 8: Fish owner loves white
fish_idx = pet_to_idx['fish']
white_idx = color_to_idx['white']
for i in range(4):
    solver.add(Implies(pet_vars[i] == fish_idx, color_vars[i] == white_idx))

# Clue 9: Cooking to the right of red
cooking_idx = hobby_to_idx['cooking']
solver.add(Or([And(hobby_vars[i] == cooking_idx, color_vars[j] == red_idx, i > j) for i in range(4) for j in range(4)]))

# Clue 10: White lover has carnations
carnations_idx = flower_to_idx['carnations']
for i in range(4):
    solver.add(Implies(color_vars[i] == white_idx, flower_vars[i] == carnations_idx))

# Clue 11: White lover to the right of gardening
gardening_idx = hobby_to_idx['gardening']
solver.add(Or([And(color_vars[i] == white_idx, hobby_vars[j] == gardening_idx, i > j) for i in range(4) for j in range(4)]))

# Clue 12: Daffodils lover has yellow
yellow_idx = color_to_idx['yellow']
for i in range(4):
    solver.add(Implies(flower_vars[i] == daffodils_idx, color_vars[i] == yellow_idx))

# Clue 13: Colonial has red
colonial_idx = style_to_idx['colonial']
for i in range(4):
    solver.add(Implies(style_vars[i] == colonial_idx, color_vars[i] == red_idx))

# Clue 14: Eric has cat
cat_idx = pet_to_idx['cat']
for i in range(4):
    solver.add(Implies(name_vars[i] == eric_idx, pet_vars[i] == cat_idx))

if solver.check() == sat:
    model = solver.model()
    solution_rows = []
    for i in range(4):
        house_num = i + 1
        name = idx_to_name[model[name_vars[i]].as_long()]
        flower = idx_to_flower[model[flower_vars[i]].as_long()]
        hobby = idx_to_hobby[model[hobby_vars[i]].as_long()]
        pet = idx_to_pet[model[pet_vars[i]].as_long()]
        color = idx_to_color[model[color_vars[i]].as_long()]
        style = idx_to_style[model[style_vars[i]].as_long()]
        solution_rows.append([str(house_num), name, flower, hobby, pet, color, style])
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
            "rows": solution_rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")