from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = range(1, 6)
names = ['Eric', 'Peter', 'Arnold', 'Bob', 'Alice']
house_styles = ['modern', 'craftsman', 'ranch', 'victorian', 'colonial']
mothers = ['Penny', 'Kailyn', 'Holly', 'Janelle', 'Aniya']
phone_models = ['oneplus 9', 'google pixel 6', 'huawei p50', 'iphone 13', 'samsung galaxy s21']
drinks = ['coffee', 'water', 'root beer', 'tea', 'milk']
animals = ['fish', 'dog', 'horse', 'bird', 'cat']

# Declare variables for each attribute
name_vars = {house: Int(f'name_{house}') for house in houses}
style_vars = {house: Int(f'style_{house}') for house in houses}
mother_vars = {house: Int(f'mother_{house}') for house in houses}
phone_vars = {house: Int(f'phone_{house}') for house in houses}
drink_vars = {house: Int(f'drink_{house}') for house in houses}
animal_vars = {house: Int(f'animal_{house}') for house in houses}

# Map values to integers
name_map = {name: i for i, name in enumerate(names)}
style_map = {style: i for i, style in enumerate(house_styles)}
mother_map = {mother: i for i, mother in enumerate(mothers)}
phone_map = {phone: i for i, phone in enumerate(phone_models)}
drink_map = {drink: i for i, drink in enumerate(drinks)}
animal_map = {animal: i for i, animal in enumerate(animals)}

# Add constraints for unique values per attribute
for var_dict in [name_vars, style_vars, mother_vars, phone_vars, drink_vars, animal_vars]:
    solver.add(Distinct(var_dict.values()))

# Add constraints based on clues
# Clue 1
solver.add(phone_vars[1] != phone_map['google pixel 6'])

# Clue 2
solver.add(drink_vars[name_map['Alice']] == drink_map['water'])

# Clue 3
solver.add(style_vars[phone_map['huawei p50']] < style_vars[style_map['colonial']])

# Clue 4 and Clue 12
solver.add(animal_vars[phone_map['oneplus 9']] == animal_map['horse'])
solver.add(style_vars[phone_map['oneplus 9']] == style_map['modern'])

# Clue 5
solver.add(mother_vars[style_map['ranch']] == mother_map['Kailyn'])

# Clue 6 and Clue 20
solver.add(drink_vars[drink_map['root beer']] == animal_vars[animal_map['cat']])
solver.add(name_vars[drink_vars[drink_map['root beer']]] == name_map['Peter'])

# Clue 7
solver.add(style_vars[style_map['colonial']] != 3)

# Clue 8 and Clue 17
solver.add(animal_vars[3] == animal_map['bird'])
solver.add(drink_vars[3] == drink_map['tea'])

# Clue 9 and Clue 17
solver.add(drink_vars[name_map['Bob']] == drink_map['tea'])

# Clue 10
solver.add(mother_vars[style_map['colonial']] > mother_vars[mother_map['Kailyn']])

# Clue 11
solver.add(drink_vars[drink_map['root beer']] < mother_vars[mother_map['Kailyn']])

# Clue 13 and Clue 14
solver.add(phone_vars[phone_map['iphone 13']] == drink_vars[drink_map['milk']])
solver.add(animal_vars[drink_vars[drink_map['milk']]] == animal_map['dog'])

# Clue 15
solver.add(phone_vars[phone_map['google pixel 6']] == style_vars[style_map['craftsman']])

# Clue 16
solver.add(name_vars[1] != name_map['Eric'])

# Clue 18
solver.add(animal_vars[3] == animal_map['bird'])

# Clue 19
solver.add(mother_vars[style_map['modern']] == mother_map['Penny'])

# Clue 21
solver.add(mother_vars[3] != mother_map['Aniya'])

# Clue 22
solver.add(mother_vars[mother_map['Janelle']] == drink_vars[drink_map['water']])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution
    solution = []
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        style = house_styles[model.evaluate(style_vars[house]).as_long()]
        mother = mothers[model.evaluate(mother_vars[house]).as_long()]
        phone = phone_models[model.evaluate(phone_vars[house]).as_long()]
        drink = drinks[model.evaluate(drink_vars[house]).as_long()]
        animal = animals[model.evaluate(animal_vars[house]).as_long()]
        solution.append([str(house), name, style, mother, phone, drink, animal])
    
    # Output the solution in JSON format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],' +
          f'"rows": {solution}' +
          '}'
          '}')
else:
    print("No solution found")