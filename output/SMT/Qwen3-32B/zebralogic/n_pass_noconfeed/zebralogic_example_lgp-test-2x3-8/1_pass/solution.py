from z3 import *
import json

# Create solver
s = Solver()

# Define variables for each house's attributes
name_1 = String('name_1')
name_2 = String('name_2')

birthday_1 = String('birthday_1')
birthday_2 = String('birthday_2')

mother_1 = String('mother_1')
mother_2 = String('mother_2')

# Add constraints for uniqueness and allowed values for names
s.add(Or(name_1 == "Arnold", name_1 == "Eric"))
s.add(Or(name_2 == "Arnold", name_2 == "Eric"))
s.add(name_1 != name_2)

# Add constraints for birthdays
s.add(Or(birthday_1 == "april", birthday_1 == "sept"))
s.add(Or(birthday_2 == "april", birthday_2 == "sept"))
s.add(birthday_1 != birthday_2)

# Add constraints for mothers
s.add(Or(mother_1 == "Aniya", mother_1 == "Holly"))
s.add(Or(mother_2 == "Aniya", mother_2 == "Holly"))
s.add(mother_1 != mother_2)

# Add clue 2: April is in first house
s.add(birthday_1 == "april")

# Add clue 1: Eric is in house 1 and mother Holly is in house 2
s.add(name_1 == "Eric")
s.add(mother_2 == "Holly")

# Check if the constraints are satisfied
if s.check() == sat:
    model = s.model()
    
    # Extract values for house 1
    h1_name = model[name_1].as_string()
    h1_bday = model[birthday_1].as_string()
    h1_mother = model[mother_1].as_string()
    
    # Extract values for house 2
    h2_name = model[name_2].as_string()
    h2_bday = model[birthday_2].as_string()
    h2_mother = model[mother_2].as_string()
    
    # Prepare the solution in the required JSON format
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": [
                ["1", h1_name, h1_bday, h1_mother],
                ["2", h2_name, h2_bday, h2_mother]
            ]
        }
    }
    
    # Print the JSON-formatted solution
    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"solution": "No solution found."}))