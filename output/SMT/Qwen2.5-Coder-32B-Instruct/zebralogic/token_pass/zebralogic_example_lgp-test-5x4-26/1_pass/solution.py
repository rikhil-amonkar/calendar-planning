from z3 import *

# Define the houses
houses = range(1, 6)

# Define the domains for each attribute
names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
heights = ["very short", "short", "tall", "average", "very tall"]
mothers = ["Janelle", "Kailyn", "Penny", "Holly", "Aniya"]
hair_colors = ["blonde", "black", "gray", "red", "brown"]

# Create integer variables for each attribute in each house
name_vars = [Int(f"name_{i}") for i in houses]
height_vars = [Int(f"height_{i}") for i in houses]
mother_vars = [Int(f"mother_{i}") for i in houses]
hair_color_vars = [Int(f"hair_color_{i}") for i in houses]

# Create solvers
solver = Solver()

# Add domain constraints for each variable
for var in name_vars + height_vars + mother_vars + hair_color_vars:
    solver.add(var >= 0)
    solver.add(var < 5)

# All values in each attribute must be unique
solver.add(Distinct(name_vars))
solver.add(Distinct(height_vars))
solver.add(Distinct(mother_vars))
solver.add(Distinct(hair_color_vars))

# Convert names, heights, mothers, and hair_colors to integers
name_map = {name: i for i, name in enumerate(names)}
height_map = {height: i for i, height in enumerate(heights)}
mother_map = {mother: i for i, mother in enumerate(mothers)}
hair_color_map = {hair_color: i for i, hair_color in enumerate(hair_colors)}

# Add constraints based on the clues
# Clue 1: The person who is tall is The person whose mother's name is Holly.
solver.add(height_vars[mother_map["Holly"]] == height_map["tall"])

# Clue 2: There are two houses between the person who has an average height and the person who is short.
solver.add(Or(Abs(height_vars[height_map["average"]] - height_vars[height_map["short"]]) == 3))

# Clue 3: The person who has gray hair is directly left of The person whose mother's name is Janelle.
solver.add(hair_color_vars[mother_map["Janelle"] - 1] == hair_color_map["gray"])

# Clue 4: The person who has black hair is not in the fourth house.
solver.add(hair_color_vars[3] != hair_color_map["black"])

# Clue 5: Eric is the person who has black hair.
solver.add(name_vars[hair_color_map["black"]] == name_map["Eric"])

# Clue 6: The person who is very short is The person whose mother's name is Penny.
solver.add(height_vars[mother_map["Penny"]] == height_map["very short"])

# Clue 7: Eric and the person who has gray hair are next to each other.
solver.add(Or(
    Abs(name_vars[name_map["Eric"]] - hair_color_vars[hair_color_map["gray"]]) == 1,
    Abs(hair_color_vars[hair_color_map["gray"]] - name_vars[name_map["Eric"]]) == 1
))

# Clue 8: Bob is in the fifth house.
solver.add(name_vars[4] == name_map["Bob"])

# Clue 9: The person who has red hair is Peter.
solver.add(hair_color_vars[name_map["Peter"]] == hair_color_map["red"])

# Clue 10: The person whose mother's name is Kailyn is directly left of the person who is short.
solver.add(mother_vars[height_map["short"] - 1] == mother_map["Kailyn"])

# Clue 11: Arnold is the person who has brown hair.
solver.add(name_vars[hair_color_map["brown"]] == name_map["Arnold"])

# Clue 12: The person who has brown hair is somewhere to the left of The person whose mother's name is Janelle.
solver.add(name_vars[hair_color_map["brown"]] < mother_vars[mother_map["Janelle"]])

# Clue 13: The person whose mother's name is Aniya and the person who is very short are next to each other.
solver.add(Or(
    Abs(mother_vars[mother_map["Aniya"]] - height_vars[height_map["very short"]]) == 1,
    Abs(height_vars[height_map["very short"]] - mother_vars[mother_map["Aniya"]]) == 1
))

# Clue 14: The person whose mother's name is Kailyn is in the third house.
solver.add(mother_vars[2] == mother_map["Kailyn"])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = []
    for house in houses:
        name = names[model.evaluate(name_vars[house-1]).as_long()]
        height = heights[model.evaluate(height_vars[house-1]).as_long()]
        mother = mothers[model.evaluate(mother_vars[house-1]).as_long()]
        hair_color = hair_colors[model.evaluate(hair_color_vars[house-1]).as_long()]
        solution.append([str(house), name, height, mother, hair_color])
    
    # Print the solution in JSON format
    import json
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Height", "Mother", "HairColor"],
            "rows": solution
        }
    }, indent=2))
else:
    print("No solution found")