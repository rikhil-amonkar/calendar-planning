from z3 import *

# Define the variables
houses = range(1, 6)
names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
vacations = ["mountain", "city", "cruise", "beach", "camping"]
educations = ["doctorate", "high school", "bachelor", "associate", "master"]
colors = ["blue", "red", "white", "yellow", "green"]
phone_models = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
foods = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]

# Create a solver instance
solver = Solver()

# Create dictionaries to hold the variables
name_vars = {name: Int(name) for name in names}
vacation_vars = {vacation: Int(vacation) for vacation in vacations}
education_vars = {education: Int(education) for education in educations}
color_vars = {color: Int(color) for color in colors}
phone_model_vars = {phone_model: Int(phone_model) for phone_model in phone_models}
food_vars = {food: Int(food) for food in foods}

# Add constraints that each variable is in the range [1, 5]
for var_dict in [name_vars, vacation_vars, education_vars, color_vars, phone_model_vars, food_vars]:
    for var in var_dict.values():
        solver.add(var >= 1, var <= 5)

# Add constraints that all variables in each category are distinct
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(vacation_vars.values())))
solver.add(Distinct(list(education_vars.values())))
solver.add(Distinct(list(color_vars.values())))
solver.add(Distinct(list(phone_model_vars.values())))
solver.add(Distinct(list(food_vars.values())))

# Apply the clues
# Clue 1
solver.add(food_vars["stew"] != 1)

# Clue 2
solver.add(Abs(food_vars["stir fry"] - education_vars["associate"]) == 3)

# Clue 3
solver.add(vacation_vars["mountain"] == education_vars["bachelor"])

# Clue 4
solver.add(name_vars["Bob"] < education_vars["doctorate"])

# Clue 5
solver.add(phone_model_vars["samsung galaxy s21"] == 3)

# Clue 6
solver.add(name_vars["Eric"] == education_vars["doctorate"])

# Clue 7
solver.add(education_vars["doctorate"] == 3)

# Clue 8
solver.add(food_vars["stir fry"] == education_vars["bachelor"])

# Clue 9
solver.add(food_vars["pizza"] == education_vars["doctorate"])

# Clue 10
solver.add(name_vars["Peter"] < color_vars["green"])

# Clue 11
solver.add(vacation_vars["camping"] == phone_model_vars["iphone 13"])

# Clue 12
solver.add(name_vars["Alice"] == vacation_vars["cruise"])

# Clue 13
solver.add(Abs(education_vars["high school"] - phone_model_vars["samsung galaxy s21"]) == 1)

# Clue 14
solver.add(name_vars["Arnold"] == phone_model_vars["google pixel 6"])

# Clue 15
solver.add(phone_model_vars["huawei p50"] < phone_model_vars["oneplus 9"])

# Clue 16
solver.add(name_vars["Arnold"] == food_vars["grilled cheese"])

# Clue 17
solver.add(food_vars["grilled cheese"] != 4)

# Clue 18
solver.add(Abs(education_vars["bachelor"] - color_vars["red"]) == 3)

# Clue 19
solver.add(vacation_vars["city"] < vacation_vars["beach"])

# Clue 20
solver.add(color_vars["green"] != 2)

# Clue 21
solver.add(name_vars["Peter"] < color_vars["blue"])

# Clue 22
solver.add(Abs(vacation_vars["camping"] - color_vars["yellow"]) == 1)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        house_solution = [str(house)]
        for var_dict in [name_vars, vacation_vars, education_vars, color_vars, phone_model_vars, food_vars]:
            for key, value in var_dict.items():
                if model[value] == house:
                    house_solution.append(key)
        solution.append(house_solution)
    
    # Print the solution in the required format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],' +
          f'"rows": {solution}' +
          '}'
          + '}')
else:
    print("No solution found")