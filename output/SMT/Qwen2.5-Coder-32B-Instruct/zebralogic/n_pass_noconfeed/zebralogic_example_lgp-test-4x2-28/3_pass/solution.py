from z3 import *
import json

# Define the variables
names = ['Alice', 'Arnold', 'Peter', 'Eric']
colors = ['black', 'blonde', 'brown', 'red']
houses = range(1, 5)

# Create dictionaries to map variables to Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
color_vars = {house: Int(f'color_{house}') for house in houses}

# Create a solver instance
solver = Solver()

# Add constraints for unique names and colors
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([color_vars[house] for house in houses]))

# Map names and colors to integers
name_map = {name: i for i, name in enumerate(names)}
color_map = {color: i for i, color in enumerate(colors)}

# Reverse map integers to names and colors
reverse_name_map = {i: name for i, name in enumerate(names)}
reverse_color_map = {i: color for i, color in enumerate(colors)}

# Add constraints based on the clues
# Clue 1: Eric is directly left of the person who has blonde hair.
solver.add(Or(
    And(name_vars[1] == name_map['Eric'], color_vars[2] == color_map['blonde']),
    And(name_vars[2] == name_map['Eric'], color_vars[3] == color_map['blonde']),
    And(name_vars[3] == name_map['Eric'], color_vars[4] == color_map['blonde'])
))

# Clue 2: Alice and Arnold are next to each other.
solver.add(Or(
    And(name_vars[1] == name_map['Alice'], name_vars[2] == name_map['Arnold']),
    And(name_vars[2] == name_map['Alice'], name_vars[1] == name_map['Arnold']),
    And(name_vars[2] == name_map['Alice'], name_vars[3] == name_map['Arnold']),
    And(name_vars[3] == name_map['Alice'], name_vars[2] == name_map['Arnold']),
    And(name_vars[3] == name_map['Alice'], name_vars[4] == name_map['Arnold']),
    And(name_vars[4] == name_map['Alice'], name_vars[3] == name_map['Arnold'])
))

# Clue 3: Eric is the person who has brown hair.
# Find the house where Eric lives and assign him brown hair there.
eric_brown_hair_constraint = Or(
    And(name_vars[1] == name_map['Eric'], color_vars[1] == color_map['brown']),
    And(name_vars[2] == name_map['Eric'], color_vars[2] == color_map['brown']),
    And(name_vars[3] == name_map['Eric'], color_vars[3] == color_map['brown']),
    And(name_vars[4] == name_map['Eric'], color_vars[4] == color_map['brown'])
)
solver.add(eric_brown_hair_constraint)

# Clue 4: The person who has black hair is not in the first house.
solver.add(color_vars[1] != color_map['black'])

# Clue 5: Alice is in the first house.
solver.add(name_vars[1] == name_map['Alice'])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor"],
            "rows": []
        }
    }
    for house in houses:
        name_index = model.evaluate(name_vars[house]).as_long()
        color_index = model.evaluate(color_vars[house]).as_long()
        
        # Ensure the indices are within the valid range
        if 0 <= name_index < len(names) and 0 <= color_index < len(colors):
            name = reverse_name_map[name_index]
            color = reverse_color_map[color_index]
            solution["solution"]["rows"].append([str(house), name, color])
        else:
            print(f"Invalid index for house {house}: name_index={name_index}, color_index={color_index}")
    print(json.dumps(solution))
else:
    print("No solution found")