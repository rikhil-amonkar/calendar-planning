from z3 import *
import json

# Define the possible values for each attribute
names = ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter']
birthday_months = ['feb', 'mar', 'sept', 'jan', 'may', 'april']
foods = ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
heights = ['very short', 'average', 'super tall', 'short', 'very tall', 'tall']
cars = ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic']

# Create variables for each house (1-6) and each attribute
name_vars = [Int(f'name_{h}') for h in range(1, 7)]
birthday_vars = [Int(f'birthday_{h}') for h in range(1, 7)]
food_vars = [Int(f'food_{h}') for h in range(1, 7)]
height_vars = [Int(f'height_{h}') for h in range(1, 7)]
car_vars = [Int(f'car_{h}') for h in range(1, 7)]

constraints = []

# All attributes are permutations (0-5)
for vars_list in [name_vars, birthday_vars, food_vars, height_vars, car_vars]:
    for v in vars_list:
        constraints.append(And(0 <= v, v <= 5))
    constraints.append(Distinct(vars_list))

# Add constraints based on the clues
# Clue 1: Honda Civic (car 5) owner is short (height 3)
for h in range(6):
    constraints.append(Implies(car_vars[h] == 5, height_vars[h] == 3))

# Clue 2: Ford F150 (car 1) is in the fifth house
constraints.append(car_vars[4] == 1)

# Clue 3: stir fry (food 3) is left of Eric (name 2)
stir_fry_house = Sum([If(food_vars[i] == 3, i + 1, 0) for i in range(6)])
eric_house = Sum([If(name_vars[i] == 2, i + 1, 0) for i in range(6)])
constraints.append(stir_fry_house < eric_house)

# Clue 4: birthday May (4) is left of Carol (name 1)
birthday_may_house = Sum([If(birthday_vars[i] == 4, i + 1, 0) for i in range(6)])
carol_house = Sum([If(name_vars[i] == 1, i + 1, 0) for i in range(6)])
constraints.append(birthday_may_house < carol_house)

# Clue 5: very short (house 4) is left of April (birthday 5)
april_house = Sum([If(birthday_vars[i] == 5, i + 1, 0) for i in range(6)])
constraints.append(4 < april_house)

# Clue 6: BMW 3 series (car 2) not in third house
constraints.append(car_vars[2] != 2)

# Clue 7: two houses between stir fry and pizza
pizza_house = Sum([If(food_vars[i] == 5, i + 1, 0) for i in range(6)])
constraints.append(Or(stir_fry_house + 3 == pizza_house, pizza_house + 3 == stir_fry_house))

# Clue 8: soup (food 1) directly left of Eric
soup_house = Sum([If(food_vars[i] == 1, i + 1, 0) for i in range(6)])
constraints.append(eric_house == soup_house + 1)

# Clue 9: spaghetti (food 4) and birthday May (4) are adjacent
spaghetti_house = Sum([If(food_vars[i] == 4, i + 1, 0) for i in range(6)])
constraints.append(Abs(spaghetti_house - birthday_may_house) == 1)

# Clue 10: Alice (name 4) directly left of BMW (car 2)
alice_house = Sum([If(name_vars[i] == 4, i + 1, 0) for i in range(6)])
bmw_house = Sum([If(car_vars[i] == 2, i + 1, 0) for i in range(6)])
constraints.append(bmw_house == alice_house + 1)

# Clue 11: Tesla (car 3) is left of tall (height 5)
tesla_house = Sum([If(car_vars[i] == 3, i + 1, 0) for i in range(6)])
tall_house = Sum([If(height_vars[i] == 5, i + 1, 0) for i in range(6)])
constraints.append(tesla_house < tall_house)

# Clue 12: very tall (height 4) owns Toyota Camry (car 4)
for h in range(6):
    constraints.append(Implies(height_vars[h] == 4, car_vars[h] == 4))

# Clue 13: Peter (name 5) directly left of pizza
peter_house = Sum([If(name_vars[i] == 5, i + 1, 0) for i in range(6)])
constraints.append(pizza_house == peter_house + 1)

# Clue 14: stew (food 0) not in third house
constraints.append(food_vars[2] != 0)

# Clue 15: one house between Sept (birthday 2) and very short (house 4)
sept_house = Sum([If(birthday_vars[i] == 2, i + 1, 0) for i in range(6)])
constraints.append(Or(sept_house == 2, sept_house == 6))

# Clue 16: one house between March (birthday 1) and super tall (height 2)
march_house = Sum([If(birthday_vars[i] == 1, i + 1, 0) for i in range(6)])
super_tall_house = Sum([If(height_vars[i] == 2, i + 1, 0) for i in range(6)])
constraints.append(Abs(march_house - super_tall_house) == 2)

# Clue 17: tall (height 5) is Bob (name 3)
for h in range(6):
    constraints.append(Implies(height_vars[h] == 5, name_vars[h] == 3))

# Clue 18: birthday May (4) is to the right of Alice (name 4)
constraints.append(birthday_may_house > alice_house)

# Clue 19: very short in house 4
constraints.append(height_vars[3] == 0)

# Clue 20: birthday March (1) is short (height 3)
for h in range(6):
    constraints.append(Implies(birthday_vars[h] == 1, height_vars[h] == 3))

# Clue 21: Carol (name 1) owns Tesla (car 3)
for h in range(6):
    constraints.append(Implies(name_vars[h] == 1, car_vars[h] == 3))

# Clue 22: Eric (name 2) has birthday January (3)
for h in range(6):
    constraints.append(Implies(name_vars[h] == 2, birthday_vars[h] == 3))

# Solve the constraints
s = Solver()
s.add(constraints)

if s.check() == sat:
    m = s.model()
    rows = []
    for h in range(1, 7):
        house_num = h
        name_idx = m[name_vars[h-1]].as_long()
        name = names[name_idx]
        birthday_idx = m[birthday_vars[h-1]].as_long()
        birthday = birthday_months[birthday_idx]
        food_idx = m[food_vars[h-1]].as_long()
        food = foods[food_idx]
        height_idx = m[height_vars[h-1]].as_long()
        height = heights[height_idx]
        car_idx = m[car_vars[h-1]].as_long()
        car = cars[car_idx]
        rows.append([str(house_num), name, birthday, food, height, car])
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")