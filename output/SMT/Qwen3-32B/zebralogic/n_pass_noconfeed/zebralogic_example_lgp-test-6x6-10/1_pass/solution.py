from z3 import *
import json

solver = Solver()

# Define the possible values for each attribute
names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
foods = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
phones = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

# Create variables for each house (1-6) for each attribute
name_vars = [Int(f"name_{h}") for h in range(1, 7)]
food_vars = [Int(f"food_{h}") for h in range(1, 7)]
height_vars = [Int(f"height_{h}") for h in range(1, 7)]
drink_vars = [Int(f"drink_{h}") for h in range(1, 7)]
pet_vars = [Int(f"pet_{h}") for h in range(1, 7)]
phone_vars = [Int(f"phone_{h}") for h in range(1, 7)]

# Add constraints: all variables are between 0 and 5 and distinct per attribute
for var_list in [name_vars, food_vars, height_vars, drink_vars, pet_vars, phone_vars]:
    for v in var_list:
        solver.add(And(0 <= v, v <= 5))
    solver.add(Distinct(var_list))

# Add the clues as constraints
# Clue 1: iPhone 13 is in the third house
solver.add(phone_vars[2] == 3)

# Clue 2: Bob is tall
for i in range(6):
    solver.add(Implies(name_vars[i] == 1, height_vars[i] == 0))

# Clue 3: Soup is in the second house
solver.add(food_vars[1] == 3)

# Clue 4: Root beer directly left of Xiaomi Mi 11
clue4 = Or([And(drink_vars[i] == 0, phone_vars[i+1] == 1) for i in range(5)])
solver.add(clue4)

# Clue 5: Huawei P50 directly left of grilled cheese
clue5 = Or([And(phone_vars[i] == 4, food_vars[i+1] == 1) for i in range(5)])
solver.add(clue5)

# Clue 6: Stir fry lover likes milk
for i in range(6):
    solver.add(Implies(food_vars[i] == 2, drink_vars[i] == 5))

# Clue 7: Grilled cheese lover is tall
for i in range(6):
    solver.add(Implies(food_vars[i] == 1, height_vars[i] == 0))

# Clue 8: Xiaomi Mi 11 user drinks coffee
for i in range(6):
    solver.add(Implies(phone_vars[i] == 1, drink_vars[i] == 2))

# Clue 9: OnePlus 9 user is Arnold
for i in range(6):
    solver.add(Implies(phone_vars[i] == 5, name_vars[i] == 0))

# Clue 10: Rabbit is not in the fifth house
solver.add(pet_vars[4] != 5)

# Clue 11: Hamster is to the right of Google Pixel 6
for h_phone in range(6):
    cond = phone_vars[h_phone] == 2
    constraints = [pet_vars[h_pet] == 0 for h_pet in range(h_phone+1, 6)]
    solver.add(Implies(cond, Or(constraints)))

# Clue 12: Super tall has fish
for i in range(6):
    solver.add(Implies(height_vars[i] == 2, pet_vars[i] == 1))

# Clue 13: Fish is Alice
for i in range(6):
    solver.add(Implies(pet_vars[i] == 1, name_vars[i] == 3))

# Clue 14: Tea directly left of pizza
clue14 = Or([And(drink_vars[i] == 4, food_vars[i+1] == 4) for i in range(5)])
solver.add(clue14)

# Clue 15: Samsung Galaxy S21 is Carol
for i in range(6):
    solver.add(Implies(phone_vars[i] == 0, name_vars[i] == 4))

# Clue 16: Pizza lover is short
for i in range(6):
    solver.add(Implies(food_vars[i] == 4, height_vars[i] == 5))

# Clue 17: Arnold is very tall
for i in range(6):
    solver.add(Implies(name_vars[i] == 0, height_vars[i] == 4))

# Clue 18: Spaghetti lover uses Google Pixel 6
for i in range(6):
    solver.add(Implies(food_vars[i] == 5, phone_vars[i] == 2))

# Clue 19: Boba tea to the right of soup
for i in range(6):
    solver.add(Implies(drink_vars[i] == 1, i >= 2))

# Clue 20: Hamster not in fifth house
solver.add(pet_vars[4] != 0)

# Clue 21: Very tall not in second house
for i in range(6):
    solver.add(Implies(height_vars[i] == 4, i != 1))

# Clue 22: Super tall to the left of Peter
for i in range(6):
    for j in range(6):
        cond = And(height_vars[i] == 2, name_vars[j] == 2)
        solver.add(Implies(cond, i < j))

# Clue 23: Very short loves spaghetti
for i in range(6):
    solver.add(Implies(height_vars[i] == 3, food_vars[i] == 5))

# Clue 24: Bird to the left of spaghetti
for i in range(6):
    for j in range(6):
        cond = And(pet_vars[i] == 4, food_vars[j] == 5)
        solver.add(Implies(cond, i < j))

# Clue 25: Fish directly left of Eric
for i in range(5):
    solver.add(Implies(pet_vars[i] == 1, name_vars[i+1] == 5))

# Clue 26: Dog owner likes milk
for i in range(6):
    solver.add(Implies(pet_vars[i] == 3, drink_vars[i] == 5))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for h in range(1, 7):
        house_idx = h - 1
        name = names[model[name_vars[house_idx]].as_long()]
        food = foods[model[food_vars[house_idx]].as_long()]
        height = heights[model[height_vars[house_idx]].as_long()]
        drink = drinks[model[drink_vars[house_idx]].as_long()]
        pet = pets[model[pet_vars[house_idx]].as_long()]
        phone = phones[model[phone_vars[house_idx]].as_long()]
        solution.append([str(h), name, food, height, drink, pet, phone])
    
    output = {
        "solution": {
            "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")