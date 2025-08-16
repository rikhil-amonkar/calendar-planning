from z3 import *

# Define the variables
names = ['Peter', 'Alice', 'Bob', 'Eric', 'Arnold']
heights = ['very tall', 'average', 'tall', 'very short', 'short']
houses = [1, 2, 3, 4, 5]

# Create dictionaries to map names and heights to their respective variables
name_vars = {name: Int(name) for name in names}
height_vars = {height: Int(height) for height in heights}

# Create a solver instance
solver = Solver()

# Each person and height must be assigned to exactly one house
for var_dict in [name_vars, height_vars]:
    solver.add(Distinct(var_dict.values()))
    for house in houses:
        solver.add(Or([var == house for var in var_dict.values()]))

# Add the clues as constraints
# Clue 1: The person who is short is in the second house.
solver.add(height_vars['short'] == 2)

# Clue 2: Peter is directly left of Bob.
solver.add(name_vars['Peter'] + 1 == name_vars['Bob'])

# Clue 3: Eric is somewhere to the left of Peter.
solver.add(name_vars['Eric'] < name_vars['Peter'])

# Clue 4: The person who is very tall is directly left of Peter.
solver.add(height_vars['very tall'] + 1 == name_vars['Peter'])

# Clue 5: Alice is directly left of the person who has an average height.
solver.add(name_vars['Alice'] + 1 == height_vars['average'])

# Clue 6: The person who is short and the person who is very short are next to each other.
solver.add(Abs(height_vars['short'] - height_vars['very short']) == 1)

# Clue 7: The person who has an average height is in the fifth house.
solver.add(height_vars['average'] == 5)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    # Create a list to store the solution
    solution = []
    for house in houses:
        name = next(name for name, var in name_vars.items() if model.evaluate(var) == house)
        height = next(height for height, var in height_vars.items() if model.evaluate(var) == house)
        solution.append([str(house), name, height])
    
    # Format the solution as required
    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")