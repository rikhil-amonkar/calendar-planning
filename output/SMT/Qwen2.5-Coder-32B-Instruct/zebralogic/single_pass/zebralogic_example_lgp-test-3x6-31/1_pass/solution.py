from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3]
names = ['Eric', 'Peter', 'Arnold']
drinks = ['milk', 'water', 'tea']
vacations = ['mountain', 'city', 'beach']
house_styles = ['colonial', 'victorian', 'ranch']
animals = ['cat', 'bird', 'horse']
birthdays = ['jan', 'sept', 'april']

# Declare variables for each attribute
name_vars = {house: Int(f'name_{house}') for house in houses}
drink_vars = {house: Int(f'drink_{house}') for house in houses}
vacation_vars = {house: Int(f'vacation_{house}') for house in houses}
house_style_vars = {house: Int(f'house_style_{house}') for house in houses}
animal_vars = {house: Int(f'animal_{house}') for house in houses}
birthday_vars = {house: Int(f'birthday_{house}') for house in houses}

# Map each attribute to a unique integer
name_map = {name: i for i, name in enumerate(names)}
drink_map = {drink: i for i, drink in enumerate(drinks)}
vacation_map = {vacation: i for i, vacation in enumerate(vacations)}
house_style_map = {house_style: i for i, house_style in enumerate(house_styles)}
animal_map = {animal: i for i, animal in enumerate(animals)}
birthday_map = {birthday: i for i, birthday in enumerate(birthdays)}

# Add constraints for unique values per attribute
solver.add(Distinct(name_vars.values()))
solver.add(Distinct(drink_vars.values()))
solver.add(Distinct(vacation_vars.values()))
solver.add(Distinct(house_style_vars.values()))
solver.add(Distinct(animal_vars.values()))
solver.add(Distinct(birthday_vars.values()))

# Add constraints based on clues
# Clue 1
solver.add(house_style_vars[1] < drink_vars['milk'] + 1)
solver.add(house_style_vars[2] < drink_vars['milk'] + 1)

# Clue 2
solver.add(vacation_vars[1] == vacation_map['city'])
solver.add(house_style_vars[2] == house_style_map['victorian'])

# Clue 3
solver.add(birthday_vars[1] == birthday_map['jan'])
solver.add(animal_vars[2] == animal_map['cat'])

# Clue 4
solver.add(drink_vars[3] == drink_map['water'])
solver.add(vacation_vars[3] == vacation_map['mountain'])

# Clue 5
solver.add(name_vars[3] == name_map['Peter'])
solver.add(animal_vars[3] == animal_map['horse'])

# Clue 6
solver.add(vacation_vars[3] == vacation_map['beach'])
solver.add(house_style_vars[2] > vacation_vars[3])

# Clue 7
solver.add(name_vars[2] == name_map['Peter'])
solver.add(vacation_vars[2] == vacation_map['city'])

# Clue 8
solver.add(vacation_vars[3] == vacation_map['mountain'])
solver.add(birthday_vars[3] == birthday_map['april'])

# Clue 9
solver.add(name_vars[3] == name_map['Eric'])
solver.add(drink_vars[3] == drink_map['water'])

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        drink = drinks[model.evaluate(drink_vars[house]).as_long()]
        vacation = vacations[model.evaluate(vacation_vars[house]).as_long()]
        house_style = house_styles[model.evaluate(house_style_vars[house]).as_long()]
        animal = animals[model.evaluate(animal_vars[house]).as_long()]
        birthday = birthdays[model.evaluate(birthday_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, drink, vacation, house_style, animal, birthday])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")