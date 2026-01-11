from z3 import *

# Define the houses
houses = range(1, 6)

# Define the variables for each characteristic
names = ['Arnold', 'Eric', 'Alice', 'Bob', 'Peter']
vacations = ['mountain', 'city', 'cruise', 'beach', 'camping']
educations = ['doctorate', 'high school', 'bachelor', 'associate', 'master']
colors = ['blue', 'red', 'white', 'yellow', 'green']
phones = ['google pixel 6', 'iphone 13', 'oneplus 9', 'huawei p50', 'samsung galaxy s21']
foods = ['grilled cheese', 'stir fry', 'pizza', 'spaghetti', 'stew']

# Create dictionaries to hold the variables
name_vars = {house: Int(f'name_{house}') for house in houses}
vacation_vars = {house: Int(f'vacation_{house}') for house in houses}
education_vars = {house: Int(f'education_{house}') for house in houses}
color_vars = {house: Int(f'color_{house}') for house in houses}
phone_vars = {house: Int(f'phone_{house}') for house in houses}
food_vars = {house: Int(f'food_{house}') for house in houses}

# Create the solver
solver = Solver()

# Add constraints for each characteristic to be unique across houses
for var_dict, options in [(name_vars, names), (vacation_vars, vacations), (education_vars, educations), (color_vars, colors), (phone_vars, phones), (food_vars, foods)]:
    solver.add(Distinct([var_dict[house] for house in houses]))
    for house in houses:
        solver.add(var_dict[house] >= 0)
        solver.add(var_dict[house] < len(options))

# Translate clues into constraints
# Clue 1
solver.add(food_vars[1] != foods.index('stew'))

# Clue 2
for house1 in houses:
    for house2 in houses:
        if abs(house1 - house2) == 2:
            solver.add(Or(food_vars[house1] != foods.index('stir fry'), education_vars[house2] != educations.index('associate')))

# Clue 3
for house in houses:
    solver.add(Implies(vacation_vars[house] == vacations.index('mountain'), education_vars[house] == educations.index('bachelor')))

# Clue 4
for house1 in houses:
    for house2 in houses:
        if house1 > house2:
            solver.add(Implies(education_vars[house2] == educations.index('doctorate'), name_vars[house1] != names.index('Bob')))

# Clue 5
solver.add(phone_vars[3] == phones.index('samsung galaxy s21'))

# Clue 6
solver.add(education_vars[3] == educations.index('doctorate'))
solver.add(name_vars[3] == names.index('Eric'))

# Clue 7
solver.add(food_vars[3] == foods.index('pizza'))

# Clue 8
for house in houses:
    solver.add(Implies(food_vars[house] == foods.index('stir fry'), education_vars[house] == educations.index('bachelor')))

# Clue 9
solver.add(Implies(education_vars[3] == educations.index('doctorate'), food_vars[3] == foods.index('pizza')))

# Clue 10
for house1 in houses:
    for house2 in houses:
        if house1 > house2:
            solver.add(Implies(color_vars[house1] == colors.index('green'), name_vars[house2] != names.index('Peter')))

# Clue 11
for house in houses:
    solver.add(Implies(vacation_vars[house] == vacations.index('camping'), phone_vars[house] == phones.index('iphone 13')))

# Clue 12
for house in houses:
    solver.add(Implies(name_vars[house] == names.index('Alice'), vacation_vars[house] == vacations.index('cruise')))

# Clue 13
for house1 in houses:
    for house2 in houses:
        if abs(house1 - house2) == 1:
            solver.add(Implies(education_vars[house1] == educations.index('high school'), phone_vars[house2] == phones.index('samsung galaxy s21')))

# Clue 14
for house in houses:
    solver.add(Implies(phone_vars[house] == phones.index('google pixel 6'), name_vars[house] == names.index('Arnold')))

# Clue 15
for house1 in houses:
    for house2 in houses:
        if house1 > house2:
            solver.add(Implies(phone_vars[house1] == phones.index('oneplus 9'), phone_vars[house2] != phones.index('huawei p50')))

# Clue 16
for house in houses:
    solver.add(Implies(name_vars[house] == names.index('Arnold'), food_vars[house] == foods.index('grilled cheese')))

# Clue 17
solver.add(food_vars[4] != foods.index('grilled cheese'))

# Clue 18
for house1 in houses:
    for house2 in houses:
        if abs(house1 - house2) == 2:
            solver.add(Implies(education_vars[house1] == educations.index('bachelor'), color_vars[house2] != colors.index('red')))

# Clue 19
for house1 in houses:
    for house2 in houses:
        if house1 > house2:
            solver.add(Implies(vacation_vars[house1] == vacations.index('beach'), vacation_vars[house2] != vacations.index('city')))

# Clue 20
solver.add(color_vars[2] != colors.index('green'))

# Clue 21
for house1 in houses:
    for house2 in houses:
        if house1 > house2:
            solver.add(Implies(color_vars[house1] == colors.index('blue'), name_vars[house2] != names.index('Peter')))

# Clue 22
for house1 in houses:
    for house2 in houses:
        if abs(house1 - house2) == 1:
            solver.add(Implies(vacation_vars[house1] == vacations.index('camping'), color_vars[house2] != colors.index('yellow')))

# Solve the problem
if solver.check() == sat:
    m = solver.model()
    solution = []
    for house in houses:
        name = names[m[name_vars[house]].as_long()]
        vacation = vacations[m[vacation_vars[house]].as_long()]
        education = educations[m[education_vars[house]].as_long()]
        color = colors[m[color_vars[house]].as_long()]
        phone = phones[m[phone_vars[house]].as_long()]
        food = foods[m[food_vars[house]].as_long()]
        solution.append([str(house), name, vacation, education, color, phone, food])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")