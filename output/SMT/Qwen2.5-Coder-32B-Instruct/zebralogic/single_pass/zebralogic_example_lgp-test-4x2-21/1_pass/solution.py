from z3 import *

# Create variables for the problem
house_names = [Int(f'name_{i}') for i in range(1, 5)]
house_styles = [Int(f'style_{i}') for i in range(1, 5)]

# Define the domains for the variables
names = {'Eric': 0, 'Arnold': 1, 'Alice': 2, 'Peter': 3}
styles = {'craftsman': 0, 'colonial': 1, 'ranch': 2, 'victorian': 3}

# Create the solver
solver = Solver()

# Add constraints based on clues
# Clue 1: Alice is in the second house.
solver.add(house_names[1] == names['Alice'])

# Clue 2: The person residing in a Victorian house is directly left of Peter.
solver.add(And(house_styles[i] == styles['victorian'], house_names[i + 1] == names['Peter']) for i in range(3))

# Clue 3: Peter is somewhere to the right of the person in a ranch-style home.
solver.add(Or([And(house_styles[j] == styles['ranch'], house_names[i] == names['Peter']) for i in range(1, 4) for j in range(i)]))

# Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
solver.add(Or([And(house_styles[j] == styles['craftsman'], house_names[i] == names['Arnold']) for i in range(1, 4) for j in range(i)]))

# Clue 5: The person in a Craftsman-style house is Alice.
solver.add(house_styles[i] == styles['craftsman'] for i in range(4) if house_names[i] == names['Alice'])

# Ensure all names and styles are unique
solver.add(Distinct(house_names))
solver.add(Distinct(house_styles))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(4):
        name = [k for k, v in names.items() if v == model[house_names[i]].as_long()][0]
        style = [k for k, v in styles.items() if v == model[house_styles[i]].as_long()][0]
        solution.append([str(i + 1), name, style])
    
    # Print the solution in the required format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "HouseStyle"],' +
          f'"rows": {solution}' +
          '}}')
else:
    print("No solution found")