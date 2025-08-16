from z3 import Solver, Int, Or, Distinct, Implies
import json

# Create the Z3 solver instance
solver = Solver()

# There are 2 houses (House 1 and House 2).
# Each house has a Name, Birthday, and Color attribute.
# We assign integer values as follows:
# Name: 1 represents "Eric", 2 represents "Arnold"
# Birthday: 1 represents "april", 2 represents "sept"
# Color: 1 represents "yellow", 2 represents "red"

# Create Z3 variables for each house attribute.
house_names = [Int(f"house_{i}_name") for i in range(1, 3)]
house_birthdays = [Int(f"house_{i}_birthday") for i in range(1, 3)]
house_colors = [Int(f"house_{i}_color") for i in range(1, 3)]

# Each variable can only take one of the two possible values.
for i in range(2):
    solver.add(Or(house_names[i] == 1, house_names[i] == 2))
    solver.add(Or(house_birthdays[i] == 1, house_birthdays[i] == 2))
    solver.add(Or(house_colors[i] == 1, house_colors[i] == 2))

# All attributes are unique across houses.
solver.add(Distinct(house_names))
solver.add(Distinct(house_birthdays))
solver.add(Distinct(house_colors))

# Clue 1: "Eric is the person who loves yellow."
# => For the house where the Name is Eric (1), the Color must be yellow (1).
for i in range(2):
    solver.add(Implies(house_names[i] == 1, house_colors[i] == 1))

# Clue 2: "The person whose birthday is in April is in the first house."
# => House 1 must have birthday april (1).
solver.add(house_birthdays[0] == 1)

# Clue 3: "The person who loves yellow is not in the first house."
# => House 1 cannot have the color yellow (1).
solver.add(house_colors[0] != 1)

# Solve the constraints
if solver.check().r == 1:  # Check returns sat if solution exists
    model = solver.model()
else:
    raise Exception("No solution found!")

# Maps to convert the integer assignments back to strings.
name_map = {1: "Eric", 2: "Arnold"}
birthday_map = {1: "april", 2: "sept"}
color_map = {1: "yellow", 2: "red"}

# Build the result rows in the required order (House 1 then House 2)
rows = []
for i in range(2):
    house_number = str(i + 1)
    name_val = model[house_names[i]].as_long()
    birthday_val = model[house_birthdays[i]].as_long()
    color_val = model[house_colors[i]].as_long()
    row = [house_number, name_map[name_val], birthday_map[birthday_val], color_map[color_val]]
    rows.append(row)

# Construct the JSON output in the specified structure.
result = {
    "solution": {
        "header": ["House", "Name", "Birthday", "Color"],
        "rows": rows
    }
}

# Print the JSON result
print(json.dumps(result))