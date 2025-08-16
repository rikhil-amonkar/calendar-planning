from z3 import *

# Define the variables
names = ['Arnold', 'Peter', 'Eric', 'Alice']
styles = ['victorian', 'ranch', 'colonial', 'craftsman']
houses = [1, 2, 3, 4]

# Create a solver instance
solver = Solver()

# Define the arrays for names and styles
house_to_name = {h: Int(f'name_{h}') for h in houses}
house_to_style = {h: Int(f'style_{h}') for h in houses}

# Add constraints for unique names and styles
solver.add(Distinct([house_to_name[h] for h in houses]))
solver.add(Distinct([house_to_style[h] for h in houses]))

# Map names and styles to integers
name_map = {n: i for i, n in enumerate(names)}
style_map = {s: i for i, s in enumerate(styles)}

# Add the clues as constraints
# Clue 1: Eric is the person in a Craftsman-style house.
solver.add(house_to_name[3] == name_map['Eric'])
solver.add(house_to_style[3] == style_map['craftsman'])

# Clue 2: The person in a ranch-style home is directly left of the person residing in a Victorian house.
solver.add(Or(
    And(house_to_style[1] == style_map['ranch'], house_to_style[2] == style_map['victorian']),
    And(house_to_style[2] == style_map['ranch'], house_to_style[3] == style_map['victorian']),
    And(house_to_style[3] == style_map['ranch'], house_to_style[4] == style_map['victorian'])
))

# Clue 3: Eric is in the third house. (Already added in Clue 1)

# Clue 4: Arnold is in the fourth house.
solver.add(house_to_name[4] == name_map['Arnold'])

# Clue 5: The person residing in a Victorian house is Alice.
solver.add(house_to_style[2] == style_map['victorian'])  # From Clue 2, Alice must be in the second house
solver.add(house_to_name[2] == name_map['Alice'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for h in houses:
        name = names[model[house_to_name[h]].as_long()]
        style = styles[model[house_to_style[h]].as_long()]
        solution.append([str(h), name, style])
    
    # Print the solution in the required format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "HouseStyle"],' +
          f'"rows": {solution}' +
          '}'
          '}')
else:
    print("No solution found")