from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each characteristic
names = ['Peter', 'Bob', 'Carol', 'Eric', 'Alice', 'Arnold']
pets = ['bird', 'dog', 'cat', 'rabbit', 'fish', 'hamster']
house_styles = ['victorian', 'ranch', 'modern', 'mediterranean', 'colonial', 'craftsman']
birthdays = ['mar', 'sept', 'may', 'feb', 'jan', 'april']

# Create arrays for each characteristic
name_vars = [String(f'name_{i}') for i in range(6)]
pet_vars = [String(f'pet_{i}') for i in range(6)]
house_style_vars = [String(f'house_style_{i}') for i in range(6)]
birthday_vars = [String(f'birthday_{i}') for i in range(6)]

# Add domain constraints
for i in range(6):
    solver.add(name_vars[i] == Or([name for name in names]))
    solver.add(pet_vars[i] == Or([pet for pet in pets]))
    solver.add(house_style_vars[i] == Or([house_style for house_style in house_styles]))
    solver.add(birthday_vars[i] == Or([birthday for birthday in birthdays]))

# All values in each array must be distinct
solver.add(Distinct(name_vars))
solver.add(Distinct(pet_vars))
solver.add(Distinct(house_style_vars))
solver.add(Distinct(birthday_vars))

# Clue 3 & 4: The person whose birthday is in May is in the second house. The person living in a colonial-style house is in the second house.
solver.add(birthday_vars[1] == 'may')
solver.add(house_style_vars[1] == 'colonial')

# Clue 5: Carol is in the third house.
solver.add(name_vars[2] == 'Carol')

# Clue 7: The person with an aquarium of fish is somewhere to the right of Bob.
solver.add(Or([And(name_vars[i] == 'Bob', pet_vars[j] == 'fish') for i in range(5) for j in range(i+1, 6)]))

# Clue 8: Eric is in the sixth house.
solver.add(name_vars[5] == 'Eric')

# Clue 9: There is one house between the person who has a cat and the person residing in a Victorian house.
solver.add(Or([And(pet_vars[i] == 'cat', house_style_vars[i+2] == 'victorian') for i in range(4)] +
              [And(pet_vars[i] == 'cat', house_style_vars[i-2] == 'victorian') for i in range(2, 6)]))

# Clue 10: There are two houses between the person residing in a Victorian house and the person with a pet hamster.
solver.add(Or([And(house_style_vars[i] == 'victorian', pet_vars[i+3] == 'hamster') for i in range(3)] +
              [And(house_style_vars[i] == 'victorian', pet_vars[i-3] == 'hamster') for i in range(3, 6)]))

# Clue 11: The person in a Craftsman-style house is Arnold.
solver.add(house_style_vars[3] == 'craftsman')
solver.add(name_vars[3] == 'Arnold')

# Clue 12: The person living in a colonial-style house is somewhere to the left of the person in a modern-style house.
solver.add(Or([And(house_style_vars[i] == 'colonial', house_style_vars[j] == 'modern') for i in range(5) for j in range(i+1, 6)]))

# Clue 13: The person with an aquarium of fish is not in the second house.
solver.add(pet_vars[1] != 'fish')

# Clue 14: Peter is the person living in a colonial-style house.
solver.add(name_vars[1] == 'Peter')

# Clue 15: The person whose birthday is in January is directly left of the person whose birthday is in April.
solver.add(Or([And(birthday_vars[i] == 'jan', birthday_vars[i+1] == 'april') for i in range(5)]))

# Clue 16: There is one house between the person who keeps a pet bird and the person in a modern-style house.
solver.add(Or([And(pet_vars[i] == 'bird', house_style_vars[i+2] == 'modern') for i in range(4)] +
              [And(pet_vars[i] == 'bird', house_style_vars[i-2] == 'modern') for i in range(2, 6)]))

# Clue 17: Carol is the person whose birthday is in March.
solver.add(birthday_vars[2] == 'mar')

# Clue 19: The person who owns a dog is in the fourth house.
solver.add(pet_vars[3] == 'dog')

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(6):
        name = model.evaluate(name_vars[i]).as_string()[1:-1]
        pet = model.evaluate(pet_vars[i]).as_string()[1:-1]
        house_style = model.evaluate(house_style_vars[i]).as_string()[1:-1]
        birthday = model.evaluate(birthday_vars[i]).as_string()[1:-1]
        solution.append([str(i+1), name, pet, house_style, birthday])
    
    # Output the solution in JSON format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],' +
          f'"rows": {solution}' +
          '}'
          '}')
else:
    print("No solution found")