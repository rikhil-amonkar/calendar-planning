from z3 import *

# Define the variables
houses = [1, 2, 3]
names = ['Eric', 'Peter', 'Arnold']
drinks = ['milk', 'water', 'tea']
vacations = ['mountain', 'city', 'beach']
house_styles = ['colonial', 'victorian', 'ranch']
animals = ['cat', 'bird', 'horse']
birthdays = ['jan', 'sept', 'april']

# Create dictionaries to map variables to Z3 variables
name_vars = {name: Int(name) for name in names}
drink_vars = {drink: Int(drink) for drink in drinks}
vacation_vars = {vacation: Int(vacation) for vacation in vacations}
house_style_vars = {house_style: Int(house_style) for house_style in house_styles}
animal_vars = {animal: Int(animal) for animal in animals}
birthday_vars = {birthday: Int(birthday) for birthday in birthdays}

# Create a solver instance
solver = Solver()

# Add constraints for each variable to be in the range of houses
for var_dict in [name_vars, drink_vars, vacation_vars, house_style_vars, animal_vars, birthday_vars]:
    for var in var_dict.values():
        solver.add(And(var >= 1, var <= 3))

# Add constraints for all variables to be distinct
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(drink_vars.values())))
solver.add(Distinct(list(vacation_vars.values())))
solver.add(Distinct(list(house_style_vars.values())))
solver.add(Distinct(list(animal_vars.values())))
solver.add(Distinct(list(birthday_vars.values())))

# Add the clues as constraints
# Clue 1
solver.add(house_style_vars['colonial'] < drink_vars['milk'])

# Clue 2
solver.add(vacation_vars['city'] + 1 == house_style_vars['victorian'])

# Clue 3
solver.add(birthday_vars['jan'] + 1 == animal_vars['cat'])

# Clue 4
solver.add(drink_vars['water'] == vacation_vars['mountain'])

# Clue 5
solver.add(animal_vars['horse'] == name_vars['Peter'])

# Clue 6
solver.add(house_style_vars['victorian'] > vacation_vars['beach'])

# Clue 7
solver.add(vacation_vars['city'] == name_vars['Peter'])

# Clue 8
solver.add(vacation_vars['mountain'] == birthday_vars['april'])

# Clue 9
solver.add(drink_vars['water'] == name_vars['Eric'])

# Check if the solution is satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [str(house)]
        for var_dict in [name_vars, drink_vars, vacation_vars, house_style_vars, animal_vars, birthday_vars]:
            for name, var in var_dict.items():
                if model.evaluate(var) == house:
                    row.append(name)
        solution["solution"]["rows"].append(row)
    
    import json
    print(json.dumps(solution))
else:
    print("No solution found")