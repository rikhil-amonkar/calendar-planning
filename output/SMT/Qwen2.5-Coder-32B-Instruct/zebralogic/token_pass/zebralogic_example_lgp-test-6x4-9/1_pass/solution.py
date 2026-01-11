from z3 import *

# Define variables for each characteristic in each house
names = [String(f'name_{i}') for i in range(1, 7)]
phone_models = [String(f'phone_model_{i}') for i in range(1, 7)]
nationalities = [String(f'nationality_{i}') for i in range(1, 7)]
colors = [String(f'color_{i}') for i in range(1, 7)]

# Create a solver instance
solver = Solver()

# Define domains for each variable
people = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
phone_models_list = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
nationalities_list = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
colors_list = ['blue', 'red', 'yellow', 'green', 'white', 'purple']

# Add domain constraints
for i in range(6):
    solver.add(names[i] == Or(*[people[j] for j in range(6)]))
    solver.add(phone_models[i] == Or(*[phone_models_list[j] for j in range(6)]))
    solver.add(nationalities[i] == Or(*[nationalities_list[j] for j in range(6)]))
    solver.add(colors[i] == Or(*[colors_list[j] for j in range(6)]))

# Add uniqueness constraints
solver.add(Distinct(names))
solver.add(Distinct(phone_models))
solver.add(Distinct(nationalities))
solver.add(Distinct(colors))

# Clue 1: Carol is not in the third house.
solver.add(names[2] != 'Carol')

# Clue 2: There is one house between the Dane and the British person.
solver.add(Or(
    Abs(nationalities.index('dane') - nationalities.index('brit')) == 2
))

# Clue 3: Carol is the person whose favorite color is green.
solver.add(And(names[i] == 'Carol', colors[i] == 'green') for i in range(6))

# Clue 4: Arnold is directly left of Alice.
solver.add(Or(
    And(names[i] == 'Arnold', names[i + 1] == 'Alice') for i in range(5)
))

# Clue 5: Alice is the German.
solver.add(And(names[i] == 'Alice', nationalities[i] == 'german') for i in range(6))

# Clue 6: The person who uses a OnePlus 9 is the person who loves purple.
solver.add(And(phone_models[i] == 'oneplus 9', colors[i] == 'purple') for i in range(6))

# Clue 7: The person who uses a Huawei P50 is not in the third house.
solver.add(phone_models[2] != 'huawei p50')

# Clue 8: The person who uses a Samsung Galaxy S21 is in the fifth house.
solver.add(phone_models[4] == 'samsung galaxy s21')

# Clue 9: The person who loves white is somewhere to the right of the person whose favorite color is red.
solver.add(Or(
    And(colors[i] == 'red', colors[j] == 'white') for i in range(6) for j in range(i + 1, 6)
))

# Clue 10: The person who uses a Samsung Galaxy S21 is Bob.
solver.add(And(phone_models[i] == 'samsung galaxy s21', names[i] == 'Bob') for i in range(6))

# Clue 11: The Dane is the person who loves yellow.
solver.add(And(nationalities[i] == 'dane', colors[i] == 'yellow') for i in range(6))

# Clue 12: The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
solver.add(Or(
    And(phone_models[i] == 'samsung galaxy s21', names[j] == 'Peter') for i in range(5) for j in range(i + 1, 6)
))

# Clue 13: The person who loves blue is Peter.
solver.add(And(colors[i] == 'blue', names[i] == 'Peter') for i in range(6))

# Clue 14: Peter is the British person.
solver.add(And(names[i] == 'Peter', nationalities[i] == 'brit') for i in range(6))

# Clue 15: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
solver.add(Or(
    And(phone_models[i] == 'samsung galaxy s21', phone_models[i + 1] == 'iphone 13') for i in range(5)
))

# Clue 16: The Norwegian is the person who loves purple.
solver.add(And(nationalities[i] == 'norwegian', colors[i] == 'purple') for i in range(6))

# Clue 17: The person who uses a Xiaomi Mi 11 is the Chinese.
solver.add(And(phone_models[i] == 'xiaomi mi 11', nationalities[i] == 'chinese') for i in range(6))

# Check if the problem is solvable
if solver.check() == sat:
    m = solver.model()
    solution = []
    for i in range(6):
        name = m[names[i]].as_string()[1:-1]
        phone_model = m[phone_models[i]].as_string()[1:-1]
        nationality = m[nationalities[i]].as_string()[1:-1]
        color = m[colors[i]].as_string()[1:-1]
        solution.append([str(i + 1), name, phone_model, nationality, color])
    
    result = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")