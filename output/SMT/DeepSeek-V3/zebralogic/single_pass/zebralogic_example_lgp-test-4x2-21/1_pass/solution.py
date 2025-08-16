import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4]

# Define the names and house styles
names = ["Eric", "Arnold", "Alice", "Peter"]
house_styles = ["craftsman", "colonial", "ranch", "victorian"]

# Create variables for each house's name and style
name_vars = {house: String(f"name_{house}") for house in houses}
style_vars = {house: String(f"style_{house}") for house in houses}

# Add constraints that each name and style is unique
s.add(Distinct([name_vars[house] for house in houses]))
s.add(Distinct([style_vars[house] for house in houses]))

# Each name and style must be one of the allowed values
for house in houses:
    s.add(Or([name_vars[house] == name for name in names]))
    s.add(Or([style_vars[house] == style for style in house_styles]))

# Clue 1: Alice is in the second house.
s.add(name_vars[2] == "Alice")

# Clue 5: The person in a Craftsman-style house is Alice.
s.add(style_vars[2] == "craftsman")

# Clue 2: The person residing in a Victorian house is directly left of Peter.
for house in [1, 2, 3]:
    s.add(Implies(style_vars[house] == "victorian", name_vars[house + 1] == "Peter"))

# Clue 3: Peter is somewhere to the right of the person in a ranch-style home.
# This means ranch is to the left of Peter
ranch_positions = []
for house in houses:
    s.add(Implies(style_vars[house] == "ranch", Or([name_vars[h] == "Peter" for h in houses if h > house])))

# Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
# Craftsman is in house 2 (from clue 5), so Arnold must be in house 3 or 4
s.add(Or(name_vars[3] == "Arnold", name_vars[4] == "Arnold"))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": []
        }
    }
    for house in sorted(houses):
        name = model.eval(name_vars[house]).as_string()
        style = model.eval(style_vars[house]).as_string()
        solution["solution"]["rows"].append([str(house), name, style])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")