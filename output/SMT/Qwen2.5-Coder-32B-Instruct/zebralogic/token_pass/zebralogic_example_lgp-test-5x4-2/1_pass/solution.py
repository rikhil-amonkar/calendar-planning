from z3 import *

# Initialize solver
solver = Solver()

# Define variables for each characteristic for each house
houses = [1, 2, 3, 4, 5]
names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
colors = ['blue', 'green', 'white', 'yellow', 'red']
phone_models = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']

# Create variables
house_name = {h: Int(f'house_{h}_name') for h in houses}
house_color = {h: Int(f'house_{h}_color') for h in houses}
house_phone_model = {h: Int(f'house_{h}_phone_model') for h in houses}
house_occupation = {h: Int(f'house_{h}_occupation') for h in houses}

# Add domain constraints
for h in houses:
    solver.add(house_name[h] >= 0, house_name[h] < len(names))
    solver.add(house_color[h] >= 0, house_color[h] < len(colors))
    solver.add(house_phone_model[h] >= 0, house_phone_model[h] < len(phone_models))
    solver.add(house_occupation[h] >= 0, house_occupation[h] < len(occupations))

# Add uniqueness constraints
solver.add(Distinct([house_name[h] for h in houses]))
solver.add(Distinct([house_color[h] for h in houses]))
solver.add(Distinct([house_phone_model[h] for h in houses]))
solver.add(Distinct([house_occupation[h] for h in houses]))

# Apply Clues

# Clue 2: Bob is in the second house.
solver.add(house_name[2] == names.index('Bob'))

# Clue 3: The person who uses a Samsung Galaxy S21 is the person who is a doctor.
solver.add(Implies(house_phone_model[h] == phone_models.index('samsung galaxy s21'), house_occupation[h] == occupations.index('doctor')) for h in houses)

# Clue 4: The person who is a doctor is the person who loves blue.
solver.add(Implies(house_occupation[h] == occupations.index('doctor'), house_color[h] == colors.index('blue')) for h in houses)

# Clue 5: The person whose favorite color is green is not in the fifth house.
solver.add(house_color[5] != colors.index('green'))

# Clue 6: The person who is a lawyer is the person who uses a OnePlus 9.
solver.add(Implies(house_occupation[h] == occupations.index('lawyer'), house_phone_model[h] == phone_models.index('oneplus 9')) for h in houses)

# Clue 7: The person who loves blue is directly left of the person whose favorite color is red.
solver.add(Or(
    And(house_color[1] == colors.index('blue'), house_color[2] == colors.index('red')),
    And(house_color[2] == colors.index('blue'), house_color[3] == colors.index('red')),
    And(house_color[3] == colors.index('blue'), house_color[4] == colors.index('red')),
    And(house_color[4] == colors.index('blue'), house_color[5] == colors.index('red'))
))

# Clue 8: The person who is a lawyer is somewhere to the right of the person who uses a Samsung Galaxy S21.
for i in range(1, 5):
    for j in range(i+1, 6):
        solver.add(Implies(And(house_phone_model[i] == phone_models.index('samsung galaxy s21'), house_occupation[j] == occupations.index('lawyer')), True))

# Clue 9: There is one house between the person who uses a Google Pixel 6 and the person who uses a Huawei P50.
solver.add(Or(
    And(house_phone_model[1] == phone_models.index('google pixel 6'), house_phone_model[3] == phone_models.index('huawei p50')),
    And(house_phone_model[1] == phone_models.index('huawei p50'), house_phone_model[3] == phone_models.index('google pixel 6')),
    And(house_phone_model[2] == phone_models.index('google pixel 6'), house_phone_model[4] == phone_models.index('huawei p50')),
    And(house_phone_model[2] == phone_models.index('huawei p50'), house_phone_model[4] == phone_models.index('google pixel 6')),
    And(house_phone_model[3] == phone_models.index('google pixel 6'), house_phone_model[5] == phone_models.index('huawei p50')),
    And(house_phone_model[3] == phone_models.index('huawei p50'), house_phone_model[5] == phone_models.index('google pixel 6'))
))

# Clue 10: Arnold is the person who is an engineer.
solver.add(Implies(house_occupation[h] == occupations.index('engineer'), house_name[h] == names.index('Arnold')) for h in houses)

# Clue 11: Alice is the person who loves yellow.
solver.add(Implies(house_color[h] == colors.index('yellow'), house_name[h] == names.index('Alice')) for h in houses)

# Clue 12: The person who uses a Google Pixel 6 is Eric.
solver.add(Implies(house_phone_model[h] == phone_models.index('google pixel 6'), house_name[h] == names.index('Eric')) for h in houses)

# Clue 13: The person who uses a Google Pixel 6 is the person who is a teacher.
solver.add(Implies(house_phone_model[h] == phone_models.index('google pixel 6'), house_occupation[h] == occupations.index('teacher')) for h in houses)

# Clue 14: The person whose favorite color is red is somewhere to the right of the person who is a teacher.
for i in range(1, 5):
    for j in range(i+1, 6):
        solver.add(Implies(And(house_color[i] == colors.index('red'), house_occupation[j] == occupations.index('teacher')), True))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for h in houses:
        name = names[model[house_name[h]].as_long()]
        color = colors[model[house_color[h]].as_long()]
        phone_model = phone_models[model[house_phone_model[h]].as_long()]
        occupation = occupations[model[house_occupation[h]].as_long()]
        solution.append([str(h), name, color, phone_model, occupation])
    
    print({
        "solution": {
            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
            "rows": solution
        }
    })
else:
    print("No solution found")