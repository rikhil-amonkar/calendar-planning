from z3 import *
import json

# Define the variables
names = [Int(f'name_{i}') for i in range(6)]
foods = [Int(f'food_{i}') for i in range(6)]
heights = [Int(f'height_{i}') for i in range(6)]
drinks = [Int(f'drink_{i}') for i in range(6)]
pets = [Int(f'pet_{i}') for i in range(6)]
phones = [Int(f'phone_{i}') for i in range(6)]

solver = Solver()

# Add permutation constraints
for var_list in [names, foods, heights, drinks, pets, phones]:
    solver.add(Distinct(var_list))
    for v in var_list:
        solver.add(And(0 <= v, v <= 5))

# Add clues
# Clue 1: iPhone 13 is in house 3 (index 2)
solver.add(phones[2] == 3)

# Clue 3: soup in house 2 (index 1)
solver.add(foods[1] == 3)

# Clue 9: OnePlus 9 user is Arnold
for i in range(6):
    solver.add(Implies(phones[i] == 5, names[i] == 0))

# Clue 15: Samsung Galaxy S21 is Carol
for i in range(6):
    solver.add(Implies(phones[i] == 0, names[i] == 4))

# Clue 5: Huawei P50 directly left of grilled cheese
for i in range(5):
    solver.add(Implies(phones[i] == 4, foods[i+1] == 1))

# Clue 7 and 2: grilled cheese lover is tall (Bob)
for i in range(6):
    solver.add(Implies(names[i] == 1, heights[i] == 0))
    solver.add(Implies(foods[i] == 1, heights[i] == 0))

# Clue 8: Xiaomi Mi 11 is coffee drinker
for i in range(6):
    solver.add(Implies(phones[i] == 1, drinks[i] == 2))

# Clue 6: stir fry is milk
for i in range(6):
    solver.add(Implies(foods[i] == 2, drinks[i] == 5))

# Clue 26: dog is milk
for i in range(6):
    solver.add(Implies(pets[i] == 3, drinks[i] == 5))

# Clue 18: spaghetti is Google Pixel 6
for i in range(6):
    solver.add(Implies(foods[i] == 5, phones[i] == 2))

# Clue 23: spaghetti lover is very short
for i in range(6):
    solver.add(Implies(foods[i] == 5, heights[i] == 3))

# Clue 12: super tall is fish
for i in range(6):
    solver.add(Implies(heights[i] == 2, pets[i] == 1))

# Clue 13: fish is Alice
for i in range(6):
    solver.add(Implies(pets[i] == 1, names[i] == 3))

# Clue 25: fish directly left of Eric
for i in range(5):
    solver.add(Implies(pets[i] == 1, names[i+1] == 5))

# Clue 14: tea directly left of pizza
for i in range(5):
    solver.add(Implies(drinks[i] == 4, foods[i+1] == 4))

# Clue 16: pizza lover is short
for i in range(6):
    solver.add(Implies(foods[i] == 4, heights[i] == 5))

# Clue 17: Arnold is very tall
for i in range(6):
    solver.add(Implies(names[i] == 0, heights[i] == 4))

# Clue 21: very tall not in house 2 (index 1)
solver.add(heights[1] != 4)

# Clue 10: rabbit not in house 5 (index 4)
solver.add(pets[4] != 5)

# Clue 20: hamster not in house 5 (index 4)
solver.add(pets[4] != 0)

# Clue 19: boba tea to the right of soup (house 2, index 1)
for i in range(6):
    solver.add(Implies(drinks[i] == 1, i > 1))

# Clue 4: root beer directly left of Xiaomi Mi 11
for i in range(5):
    solver.add(Implies(drinks[i] == 0, phones[i+1] == 1))

# Clue 11: hamster to the right of Google Pixel 6
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(phones[j] == 2, pets[i] == 0), i > j))

# Clue 22: super tall left of Peter
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(heights[i] == 2, names[j] == 2), i < j))

# Clue 24: bird left of spaghetti
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(pets[i] == 4, foods[j] == 5), i < j))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    
    # Mapping from integer indices to strings
    name_map = {0: 'Arnold', 1: 'Bob', 2: 'Peter', 3: 'Alice', 4: 'Carol', 5: 'Eric'}
    food_map = {0: 'stew', 1: 'grilled cheese', 2: 'stir fry', 3: 'soup', 4: 'pizza', 5: 'spaghetti'}
    height_map = {0: 'tall', 1: 'average', 2: 'super tall', 3: 'very short', 4: 'very tall', 5: 'short'}
    drink_map = {0: 'root beer', 1: 'boba tea', 2: 'coffee', 3: 'water', 4: 'tea', 5: 'milk'}
    pet_map = {0: 'hamster', 1: 'fish', 2: 'cat', 3: 'dog', 4: 'bird', 5: 'rabbit'}
    phone_map = {0: 'samsung galaxy s21', 1: 'xiaomi mi 11', 2: 'google pixel 6', 3: 'iphone 13', 4: 'huawei p50', 5: 'oneplus 9'}
    
    rows = []
    for i in range(6):
        house_num = i + 1
        name_val = name_map[model[names[i]].as_long()]
        food_val = food_map[model[foods[i]].as_long()]
        height_val = height_map[model[heights[i]].as_long()]
        drink_val = drink_map[model[drinks[i]].as_long()]
        pet_val = pet_map[model[pets[i]].as_long()]
        phone_val = phone_map[model[phones[i]].as_long()]
        rows.append([str(house_num), name_val, food_val, height_val, drink_val, pet_val, phone_val])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")