from z3 import *

# Define the solver
solver = Solver()

# Define variables for names and styles
names = [String(f'name_{i}') for i in range(4)]
styles = [String(f'style_{i}') for i in range(4)]

# Define the domain of possible values
possible_names = {'Arnold', 'Peter', 'Eric', 'Alice'}
possible_styles = {'victorian', 'ranch', 'colonial', 'craftsman'}

# Add constraints for possible values
for i in range(4):
    solver.add(names[i] == Or(*[String(name) for name in possible_names]))
    solver.add(styles[i] == Or(*[String(style) for style in possible_styles]))

# Constraint 1: Eric is the person in a Craftsman-style house.
solver.add(names[2] == 'Eric')
solver.add(styles[2] == 'craftsman')

# Constraint 2: The person in a ranch-style home is directly left of the person residing in a Victorian house.
solver.add(Or([And(styles[i] == 'ranch', styles[i+1] == 'victorian') for i in range(3)]))

# Constraint 3: Eric is in the third house.
solver.add(names[2] == 'Eric')

# Constraint 4: Arnold is in the fourth house.
solver.add(names[3] == 'Arnold')

# Constraint 5: The person residing in a Victorian house is Alice.
solver.add(Or([And(names[i] == 'Alice', styles[i] == 'victorian') for i in range(4)]))

# Ensure all names and styles are unique
solver.add(Distinct(names))
solver.add(Distinct(styles))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": [
                [str(i+1), model[names[i]].as_string(), model[styles[i]].as_string()]
                for i in range(4)
            ]
        }
    }
    print(solution)
else:
    print("No solution found")