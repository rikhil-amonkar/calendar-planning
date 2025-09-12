from z3 import *
import json

# Initialize the solver
solver = Solver()

# Define variables for each house (1 to 4)
name_1 = Int('name_1')
name_2 = Int('name_2')
name_3 = Int('name_3')
name_4 = Int('name_4')

color_1 = Int('color_1')
color_2 = Int('color_2')
color_3 = Int('color_3')
color_4 = Int('color_4')

# Add constraints for distinct names and colors
solver.add(Distinct(name_1, name_2, name_3, name_4))
solver.add(Distinct(color_1, color_2, color_3, color_4))

# Ensure all name and color values are within valid ranges
for n in [name_1, name_2, name_3, name_4]:
    solver.add(And(n >= 0, n <= 3))
for c in [color_1, color_2, color_3, color_4]:
    solver.add(And(c >= 0, c <= 3))

# Clue 1: The person whose favorite color is green is in the third house.
solver.add(color_3 == 1)

# Clue 2: Peter is in the first house.
solver.add(name_1 == 0)

# Clue 3: One house between red and yellow
clue3 = Or(
    And(color_1 == 2, color_3 == 0),
    And(color_1 == 0, color_3 == 2),
    And(color_2 == 2, color_4 == 0),
    And(color_2 == 0, color_4 == 2)
)
solver.add(clue3)

# Clue 4: Arnold is directly left of Eric
clue4 = Or(
    And(name_1 == 1, name_2 == 3),
    And(name_2 == 1, name_3 == 3),
    And(name_3 == 1, name_4 == 3)
)
solver.add(clue4)

# Clue 5: Eric loves yellow
clue5 = And(
    Or(name_1 != 3, color_1 == 0),
    Or(name_2 != 3, color_2 == 0),
    Or(name_3 != 3, color_3 == 0),
    Or(name_4 != 3, color_4 == 0)
)
solver.add(clue5)

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    names = [model[name_1], model[name_2], model[name_3], model[name_4]]
    colors = [model[color_1], model[color_2], model[color_3], model[color_4]]
    
    # Mapping integer values to names and colors
    name_map = {0: 'Peter', 1: 'Arnold', 2: 'Alice', 3: 'Eric'}
    color_map = {0: 'yellow', 1: 'green', 2: 'red', 3: 'white'}
    
    rows = []
    for i in range(4):
        house_num = i + 1
        name_val = name_map[names[i].as_long()]
        color_val = color_map[colors[i].as_long()]
        rows.append([str(house_num), name_val, color_val])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")