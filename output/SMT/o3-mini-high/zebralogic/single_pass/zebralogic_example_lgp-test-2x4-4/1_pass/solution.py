from z3 import *
import json

# Define the possible values with our chosen mappings.
# For Name: 0 = Eric, 1 = Arnold
Names = ["Eric", "Arnold"]
# For HouseStyle: 0 = victorian, 1 = colonial
HouseStyles = ["victorian", "colonial"]
# For Height: 0 = short, 1 = very short
Heights = ["short", "very short"]
# For Education: 0 = associate, 1 = high school
Educations = ["associate", "high school"]

# We have 2 houses (index 0 represents House 1, index 1 represents House 2).
name_vars = [Int(f"name_{i}") for i in range(2)]
style_vars = [Int(f"style_{i}") for i in range(2)]
height_vars = [Int(f"height_{i}") for i in range(2)]
education_vars = [Int(f"education_{i}") for i in range(2)]

s = Solver()

# Each variable is either 0 or 1.
for var in name_vars + style_vars + height_vars + education_vars:
    s.add(Or(var == 0, var == 1))

# All attributes must be unique across houses.
s.add(name_vars[0] != name_vars[1])
s.add(style_vars[0] != style_vars[1])
s.add(height_vars[0] != height_vars[1])
s.add(education_vars[0] != education_vars[1])

# Clue 2: The person residing in a Victorian house is in the first house.
# In our mapping, "victorian" is 0.
s.add(style_vars[0] == 0)

# Clue 1: The person who is short is directly left of Eric.
# With only two houses, the only possibility is that House 1 (index 0) is short 
# and House 2 (index 1) is Eric.
s.add(height_vars[0] == 0)  # House 1 must be "short" (0)
s.add(name_vars[1] == 0)    # House 2 must be "Eric" (0)

# Clue 3: The person who is short is the person with an associate's degree.
# Therefore, the house with "short" (House 1) must have education "associate" (0).
s.add(education_vars[0] == 0)

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    result_rows = []
    for i in range(2):
        row = [
            str(i + 1),
            Names[m[name_vars[i]].as_long()],
            HouseStyles[m[style_vars[i]].as_long()],
            Heights[m[height_vars[i]].as_long()],
            Educations[m[education_vars[i]].as_long()]
        ]
        result_rows.append(row)

    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": result_rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")