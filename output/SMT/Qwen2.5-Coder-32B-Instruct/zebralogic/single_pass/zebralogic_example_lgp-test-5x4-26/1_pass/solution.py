from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = range(1, 6)
names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
heights = ["very short", "short", "tall", "average", "very tall"]
mothers = ["Janelle", "Kailyn", "Penny", "Holly", "Aniya"]
hair_colors = ["blonde", "black", "gray", "red", "brown"]

# Create dictionaries to map each attribute to a variable
name_vars = {house: Int(f'name_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}
mother_vars = {house: Int(f'mother_{house}') for house in houses}
hair_color_vars = {house: Int(f'hair_color_{house}') for house in houses}

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))
solver.add(Distinct([mother_vars[house] for house in houses]))
solver.add(Distinct([hair_color_vars[house] for house in houses]))

# Map string values to integers for encoding
name_map = {name: i for i, name in enumerate(names)}
height_map = {height: i for i, height in enumerate(heights)}
mother_map = {mother: i for i, mother in enumerate(mothers)}
hair_color_map = {hair_color: i for i, hair_color in enumerate(hair_colors)}

# Add specific constraints based on the clues
# Clue 1
solver.add(height_vars[houses[mother_map["Holly"] + 1]] == height_map["tall"])

# Clue 2
for i in range(len(houses) - 2):
    solver.add(Or(
        And(height_vars[houses[i]] == height_map["average"], height_vars[houses[i + 2 + 1]] == height_map["short"]),
        And(height_vars[houses[i + 2 + 1]] == height_map["average"], height_vars[houses[i]] == height_map["short"])
    ))

# Clue 3
for i in range(len(houses) - 1):
    solver.add(Implies(hair_color_vars[houses[i]] == hair_color_map["gray"], mother_vars[houses[i + 1]] == mother_map["Janelle"]))

# Clue 4
solver.add(name_vars[4] != name_map["Eric"])

# Clue 5
solver.add(name_vars[hair_color_map["black"] + 1] == name_map["Eric"])

# Clue 6
solver.add(mother_vars[hair_color_map["very short"] + 1] == mother_map["Penny"])

# Clue 7
for i in range(len(houses) - 1):
    solver.add(Or(
        And(name_vars[houses[i]] == name_map["Eric"], hair_color_vars[houses[i + 1]] == hair_color_map["gray"]),
        And(hair_color_vars[houses[i]] == hair_color_map["gray"], name_vars[houses[i + 1]] == name_map["Eric"])
    ))

# Clue 8
solver.add(name_vars[5] == name_map["Bob"])

# Clue 9
solver.add(hair_color_vars[hair_color_map["red"] + 1] == name_map["Peter"])

# Clue 10
solver.add(Implies(mother_vars[3] == mother_map["Kailyn"], height_vars[4] == height_map["short"]))

# Clue 11
solver.add(hair_color_vars[hair_color_map["brown"] + 1] == name_map["Arnold"])

# Clue 12
for i in range(4):
    solver.add(Implies(hair_color_vars[houses[i]] == hair_color_map["brown"], mother_vars[houses[i + 1]] != mother_map["Janelle"]))

# Clue 13
for i in range(4):
    solver.add(Or(
        And(mother_vars[houses[i]] == mother_map["Aniya"], height_vars[houses[i + 1]] == height_map["very short"]),
        And(height_vars[houses[i]] == height_map["very short"], mother_vars[houses[i + 1]] == mother_map["Aniya"])
    ))

# Clue 14
solver.add(mother_vars[3] == mother_map["Kailyn"])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        height = heights[model.evaluate(height_vars[house]).as_long()]
        mother = mothers[model.evaluate(mother_vars[house]).as_long()]
        hair_color = hair_colors[model.evaluate(hair_color_vars[house]).as_long()]
        solution.append([str(house), name, height, mother, hair_color])
    
    print({
        "solution": {
            "header": ["House", "Name", "Height", "Mother", "HairColor"],
            "rows": solution
        }
    })
else:
    print("No solution found")