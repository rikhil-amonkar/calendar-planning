from z3 import *

# Define the variables for each attribute for each house
names = [Int(f'name_{i}') for i in range(3)]
drinks = [Int(f'drink_{i}') for i in range(3)]
vacations = [Int(f'vacation_{i}') for i in range(3)]
house_styles = [Int(f'house_style_{i}') for i in range(3)]
animals = [Int(f'animal_{i}') for i in range(3)]
birthdays = [Int(f'birthday_{i}') for i in range(3)]

# Define the domains for each variable
domains = {
    'names': ['Eric', 'Peter', 'Arnold'],
    'drinks': ['milk', 'water', 'tea'],
    'vacations': ['mountain', 'city', 'beach'],
    'house_styles': ['colonial', 'victorian', 'ranch'],
    'animals': ['cat', 'bird', 'horse'],
    'birthdays': ['jan', 'sept', 'april']
}

# Create mappings from strings to integers
name_map = {name: i for i, name in enumerate(domains['names'])}
drink_map = {drink: i for i, drink in enumerate(domains['drinks'])}
vacation_map = {vacation: i for i, vacation in enumerate(domains['vacations'])}
house_style_map = {house_style: i for i, house_style in enumerate(domains['house_styles'])}
animal_map = {animal: i for i, animal in enumerate(domains['animals'])}
birthday_map = {birthday: i for i, birthday in enumerate(domains['birthdays'])}

# Reverse mappings from integers to strings
name_reverse_map = {i: name for name, i in name_map.items()}
drink_reverse_map = {i: drink for drink, i in drink_map.items()}
vacation_reverse_map = {i: vacation for vacation, i in vacation_map.items()}
house_style_reverse_map = {i: house_style for house_style, i in house_style_map.items()}
animal_reverse_map = {i: animal for animal, i in animal_map.items()}
birthday_reverse_map = {i: birthday for birthday, i in birthday_map.items()}

# Create the solver
solver = Solver()

# Add constraints for unique values for each attribute across houses
solver.add(Distinct(names))
solver.add(Distinct(drinks))
solver.add(Distinct(vacations))
solver.add(Distinct(house_styles))
solver.add(Distinct(animals))
solver.add(Distinct(birthdays))

# Add constraints based on the clues
# Clue 1
solver.add(Or(house_styles[0] == house_style_map['colonial'], house_styles[1] == house_style_map['colonial']))
solver.add(Or(drinks[1] == drink_map['milk'], drinks[2] == drink_map['milk']))

# Clue 2
solver.add(vacations[0] == vacation_map['city'])
solver.add(house_styles[1] == house_style_map['victorian'])

# Clue 3
solver.add(birthdays[0] == birthday_map['jan'])
solver.add(animals[1] == animal_map['cat'])

# Clue 4
solver.add(drinks[i] == drink_map['water'] == vacations[i] == vacation_map['mountain'] for i in range(3))

# Clue 5
solver.add(animals[name_map['Peter']] == animal_map['horse'])

# Clue 6
solver.add(vacations[1] == vacation_map['beach'])
solver.add(house_styles[2] == house_style_map['victorian'])

# Clue 7
solver.add(vacations[name_map['Peter']] == vacation_map['city'])

# Clue 8
solver.add(drinks[i] == drink_map['water'] == birthdays[i] == birthday_map['april'] for i in range(3))

# Clue 9
solver.add(drinks[name_map['Eric']] == drink_map['water'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(3):
        house_number = str(i + 1)
        name = name_reverse_map[model.evaluate(names[i]).as_long()]
        drink = drink_reverse_map[model.evaluate(drinks[i]).as_long()]
        vacation = vacation_reverse_map[model.evaluate(vacations[i]).as_long()]
        house_style = house_style_reverse_map[model.evaluate(house_styles[i]).as_long()]
        animal = animal_reverse_map[model.evaluate(animals[i]).as_long()]
        birthday = birthday_reverse_map[model.evaluate(birthdays[i]).as_long()]
        solution.append([house_number, name, drink, vacation, house_style, animal, birthday])
    
    print({
        "solution": {
            "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
            "rows": solution
        }
    })
else:
    print("No solution found")