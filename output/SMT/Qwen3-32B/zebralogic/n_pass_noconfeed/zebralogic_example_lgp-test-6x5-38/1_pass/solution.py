from z3 import *
import json

solver = Solver()

names = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
heights = ["very short", "average", "super tall", "short", "very tall", "tall"]
cars = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

# Create variables for each house (0-5) and each attribute
name_vars = [String(f"name_{i}") for i in range(6)]
birthday_vars = [String(f"birthday_{i}") for i in range(6)]
food_vars = [String(f"food_{i}") for i in range(6)]
height_vars = [String(f"height_{i}") for i in range(6)]
car_vars = [String(f"car_{i}") for i in range(6)]

# Add constraints that all in each category are distinct
for vars_list in [name_vars, birthday_vars, food_vars, height_vars, car_vars]:
    solver.add(Distinct(vars_list))

# Add clues
# Clue 1: Honda Civic owner is short
for i in range(6):
    solver.add(Implies(car_vars[i] == 'honda civic', height_vars[i] == 'short'))

# Clue 2: Ford F-150 is in fifth house (index 4)
solver.add(car_vars[4] == 'ford f150')

# Clue 3: stir fry is left of Eric
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(food_vars[i] == 'stir fry', name_vars[j] == 'Eric'), i < j))

# Clue 4: May birthday is left of Carol
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(birthday_vars[i] == 'may', name_vars[j] == 'Carol'), i < j))

# Clue 5: very short is left of April birthday
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(height_vars[i] == 'very short', birthday_vars[j] == 'april'), i < j))

# Clue 6: BMW 3 series not in third house (index 2)
solver.add(car_vars[2] != 'bmw 3 series')

# Clue 7: two houses between stir fry and pizza
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(food_vars[i] == 'stir fry', food_vars[j] == 'pizza'), Or(j == i + 3, i == j + 3)))

# Clue 8: soup directly left of Eric
for i in range(5):
    solver.add(Implies(food_vars[i] == 'soup', name_vars[i+1] == 'Eric'))

# Clue 9: spaghetti and may birthday are adjacent
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(food_vars[i] == 'spaghetti', birthday_vars[j] == 'may'), Or(j == i + 1, j == i - 1)))

# Clue 10: Alice directly left of BMW 3 series
for i in range(5):
    solver.add(Implies(name_vars[i] == 'Alice', car_vars[i+1] == 'bmw 3 series'))

# Clue 11: Tesla model 3 left of tall
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(car_vars[i] == 'tesla model 3', height_vars[j] == 'tall'), i < j))

# Clue 12: very tall owns Toyota Camry
for i in range(6):
    solver.add(Implies(height_vars[i] == 'very tall', car_vars[i] == 'toyota camry'))

# Clue 13: Peter directly left of pizza
for i in range(5):
    solver.add(Implies(name_vars[i] == 'Peter', food_vars[i+1] == 'pizza'))

# Clue 14: stew not in third house (index 2)
solver.add(food_vars[2] != 'stew')

# Clue 15: one house between sept birthday and very short
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(birthday_vars[i] == 'sept', height_vars[j] == 'very short'), Or(i == j + 2, j == i + 2)))

# Clue 16: one house between mar birthday and super tall
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(birthday_vars[i] == 'mar', height_vars[j] == 'super tall'), Or(i == j + 2, j == i + 2)))

# Clue 17: tall is Bob
for i in range(6):
    solver.add(Implies(height_vars[i] == 'tall', name_vars[i] == 'Bob'))

# Clue 18: may birthday is right of Alice
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(birthday_vars[i] == 'may', name_vars[j] == 'Alice'), i > j))

# Clue 19: very short is in house 4 (index 3)
solver.add(height_vars[3] == 'very short')

# Clue 20: mar birthday is short
for i in range(6):
    solver.add(Implies(birthday_vars[i] == 'mar', height_vars[i] == 'short'))

# Clue 21: Carol owns Tesla model 3
for i in range(6):
    solver.add(Implies(name_vars[i] == 'Carol', car_vars[i] == 'tesla model 3'))

# Clue 22: Eric's birthday is jan
for i in range(6):
    solver.add(Implies(name_vars[i] == 'Eric', birthday_vars[i] == 'jan'))

if solver.check() == sat:
    model = solver.model()
    solution_rows = []
    for i in range(6):
        house_num = str(i + 1)
        name = model[name_vars[i]].as_string()
        birthday = model[birthday_vars[i]].as_string()
        food = model[food_vars[i]].as_string()
        height = model[height_vars[i]].as_string()
        car = model[car_vars[i]].as_string()
        solution_rows.append([house_num, name, birthday, food, height, car])
    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
            "rows": solution_rows
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")