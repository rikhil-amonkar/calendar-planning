from z3 import *

# Define the solver
solver = Solver()

# Define variables for each house
names = [String(f"Name_{i}") for i in range(1, 7)]
hair_colors = [String(f"HairColor_{i}") for i in range(1, 7)]
heights = [String(f"Height_{i}") for i in range(1, 7)]

# Define the domains for each variable
people = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
hair_colors_list = ["auburn", "blonde", "brown", "black", "red", "gray"]
heights_list = ["very tall", "average", "very short", "tall", "super tall", "short"]

# Add constraints for unique values
solver.add(Distinct(names))
solver.add(Distinct(hair_colors))
solver.add(Distinct(heights))

# Translate clues into constraints
# Clue 1
for i in range(5):
    solver.add(Implies(hair_colors[i] == "blonde", names[i+1] == "Bob"))

# Clue 2
solver.add(names[3] == "Alice")

# Clue 3
for i in range(6):
    solver.add(Implies(heights[i] == "short", names[i] == "Arnold"))

# Clue 4
solver.add(heights[5] == "tall")

# Clue 5
solver.add(hair_colors[3] != "black")

# Clue 6
for i in range(6):
    solver.add(Implies(hair_colors[i] == "red", names[i] == "Eric"))

# Clue 7
for i in range(5):
    solver.add(Implies(heights[i] == "average", Or([heights[j] == "super tall" for j in range(i+1, 6)])))

# Clue 8
for i in range(6):
    solver.add(Implies(hair_colors[i] == "blonde", names[i] == "Carol"))

# Clue 9
for i in range(1, 5):
    solver.add(Implies(hair_colors[i] == "gray", hair_colors[i+2] == "red"))
for i in range(3, 6):
    solver.add(Implies(hair_colors[i] == "gray", hair_colors[i-2] == "red"))

# Clue 10
solver.add(heights[4] == "very short")

# Clue 11
for i in range(6):
    solver.add(Implies(names[i] == "Bob", hair_colors[i] == "brown"))

# Clue 12
solver.add(hair_colors[2] == "gray")

# Clue 13
for i in range(6):
    solver.add(Implies(hair_colors[i] == "blonde", heights[i] == "very tall"))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(6):
        house = str(i + 1)
        name = model[names[i]].as_string()[1:-1]  # Remove quotes
        hair_color = model[hair_colors[i]].as_string()[1:-1]  # Remove quotes
        height = model[heights[i]].as_string()[1:-1]  # Remove quotes
        solution.append([house, name, hair_color, height])
    
    # Format the solution as JSON
    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")