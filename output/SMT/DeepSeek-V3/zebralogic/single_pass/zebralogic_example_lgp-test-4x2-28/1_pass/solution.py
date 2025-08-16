from z3 import *
import json

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4]

# Define the names and hair colors
names = ["Alice", "Arnold", "Peter", "Eric"]
hair_colors = ["black", "blonde", "brown", "red"]

# Create variables for each house's name and hair color
name_vars = {house: String(f"name_{house}") for house in houses}
hair_vars = {house: String(f"hair_{house}") for house in houses}

# Add constraints for uniqueness of names and hair colors
s.add(Distinct([name_vars[house] for house in houses]))
s.add(Distinct([hair_vars[house] for house in houses]))

# Each name and hair color must be one of the allowed values
for house in houses:
    s.add(Or([name_vars[house] == name for name in names]))
    s.add(Or([hair_vars[house] == color for color in hair_colors]))

# Clue 5: Alice is in the first house
s.add(name_vars[1] == "Alice")

# Clue 4: The person who has black hair is not in the first house
s.add(hair_vars[1] != "black")

# Clue 3: Eric is the person who has brown hair
for house in houses:
    s.add(Implies(name_vars[house] == "Eric", hair_vars[house] == "brown"))

# Clue 1: Eric is directly left of the person who has blonde hair
for i in range(1, 4):
    s.add(Implies(name_vars[i] == "Eric", hair_vars[i+1] == "blonde"))

# Clue 2: Alice and Arnold are next to each other
# Since Alice is in house 1, Arnold must be in house 2
s.add(name_vars[2] == "Arnold")

# Solve the constraints
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor"],
            "rows": []
        }
    }
    for house in sorted(houses):
        name = model.eval(name_vars[house])
        hair = model.eval(hair_vars[house])
        solution["solution"]["rows"].append([str(house), str(name), str(hair)])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")