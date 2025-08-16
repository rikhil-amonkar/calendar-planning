from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3, 4]
names = ['Eric', 'Alice', 'Peter', 'Arnold']
hair_colors = ['blonde', 'black', 'red', 'brown']
favorite_sports = ['swimming', 'soccer', 'basketball', 'tennis']

# Create dictionaries to map variables to Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
hair_color_vars = {house: Int(f'hair_color_{house}') for house in houses}
favorite_sport_vars = {house: Int(f'favorite_sport_{house}') for house in houses}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([hair_color_vars[house] for house in houses]))
solver.add(Distinct([favorite_sport_vars[house] for house in houses]))

# Map names, hair colors, and favorite sports to integers
name_map = {name: i for i, name in enumerate(names)}
hair_color_map = {color: i for i, color in enumerate(hair_colors)}
favorite_sport_map = {sport: i for i, sport in enumerate(favorite_sports)}

# Add clues as constraints
# Clue 1: The person who loves soccer is not in the second house.
solver.add(favorite_sport_vars[2] != favorite_sport_map['soccer'])

# Clue 2: Eric is the person who has blonde hair.
solver.add(name_vars[house] == name_map['Eric'] for house in houses if solver.check() == sat)
solver.add(hair_color_vars[house] == hair_color_map['blonde'] for house in houses if solver.check() == sat)

# Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
for i in range(4):
    for j in range(i+1, 4):
        solver.add(Or(hair_color_vars[j] != hair_color_map['blonde'], favorite_sport_vars[i] != favorite_sport_map['basketball']))

# Clue 4: The person who has black hair is the person who loves tennis.
solver.add(And([hair_color_vars[house] == hair_color_map['black'] == favorite_sport_vars[house] == favorite_sport_map['tennis'] for house in houses if solver.check() == sat]))

# Clue 5: Arnold is somewhere to the left of the person who has red hair.
for i in range(4):
    for j in range(i+1, 4):
        solver.add(Or(name_vars[i] != name_map['Arnold'], hair_color_vars[j] != hair_color_map['red']))

# Clue 6: Alice is the person who loves swimming.
solver.add(name_vars[house] == name_map['Alice'] for house in houses if solver.check() == sat)
solver.add(favorite_sport_vars[house] == favorite_sport_map['swimming'] for house in houses if solver.check() == sat)

# Clue 7: The person who has red hair is directly left of the person who has black hair.
for i in range(3):
    solver.add(Or(hair_color_vars[i] != hair_color_map['red'], hair_color_vars[i+1] != hair_color_map['black']))

# Check if the solution is satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        hair_color = hair_colors[model[hair_color_vars[house]].as_long()]
        favorite_sport = favorite_sports[model[favorite_sport_vars[house]].as_long()]
        solution.append([str(house), name, hair_color, favorite_sport])
    
    # Print the solution in the required JSON format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "HairColor", "FavoriteSport"],' +
          f'"rows": {solution}' +
          '}'
          '}')
else:
    print("No solution found")