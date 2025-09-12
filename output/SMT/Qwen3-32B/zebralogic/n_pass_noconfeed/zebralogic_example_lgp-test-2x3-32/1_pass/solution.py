import json
from z3 import *

# Define the Enum sorts
Name, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
Birthday, (April, Sept) = EnumSort('Birthday', ['april', 'sept'])
Color, (Yellow, Red) = EnumSort('Color', ['yellow', 'red'])

# Create variables for each house's attributes
name1 = Const('name1', Name)
birthday1 = Const('birthday1', Birthday)
color1 = Const('color1', Color)

name2 = Const('name2', Name)
birthday2 = Const('birthday2', Birthday)
color2 = Const('color2', Color)

solver = Solver()

# Add uniqueness constraints
solver.add(name1 != name2)
solver.add(birthday1 != birthday2)
solver.add(color1 != color2)

# Add puzzle constraints
# Clue 2: The person whose birthday is in April is in the first house.
solver.add(birthday1 == April)

# Clue 3: The person who loves yellow is not in the first house.
solver.add(color1 != Yellow)

# Clue 1: Eric is the person who loves yellow.
solver.add(Implies(name1 == Eric, color1 == Yellow))
solver.add(Implies(name2 == Eric, color2 == Yellow))

if solver.check() == sat:
    model = solver.model()
    
    # Extract values for each house
    h1_name = str(model[name1])
    h1_bday = str(model[birthday1])
    h1_color = str(model[color1])
    
    h2_name = str(model[name2])
    h2_bday = str(model[birthday2])
    h2_color = str(model[color2])
    
    # Construct the solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": [
                ["1", h1_name, h1_bday, h1_color],
                ["2", h2_name, h2_bday, h2_color]
            ]
        }
    }
    
    # Output as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")