from z3 import *

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the domains
names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
heights = ["average", "very short", "short", "very tall", "tall"]

# Create variables
name_vars = {h: Int(f"name_{h}") for h in houses}
mother_vars = {h: Int(f"mother_{h}") for h in houses}
height_vars = {h: Int(f"height_{h}") for h in houses}

# Define the solver
solver = Solver()

# Add constraints for uniqueness within each category
solver.add(Distinct([name_vars[h] for h in houses]))
solver.add(Distinct([mother_vars[h] for h in houses]))
solver.add(Distinct([height_vars[h] for h in houses]))

# Map values to integers
name_map = {n: i for i, n in enumerate(names)}
mother_map = {m: i for i, m in enumerate(mothers)}
height_map = {h: i for i, h in enumerate(heights)}

# Add constraints based on clues
# Clue 1
solver.add(Implies(name_vars[1] == name_map["Alice"], mother_vars[1] == mother_map["Aniya"]))
solver.add(Implies(name_vars[2] == name_map["Alice"], mother_vars[2] == mother_map["Aniya"]))
solver.add(Implies(name_vars[3] == name_map["Alice"], mother_vars[3] == mother_map["Aniya"]))
solver.add(Implies(name_vars[4] == name_map["Alice"], mother_vars[4] == mother_map["Aniya"]))
solver.add(Implies(name_vars[5] == name_map["Alice"], mother_vars[5] == mother_map["Aniya"]))

# Clue 2
for h in range(1, 5):
    solver.add(Implies(height_vars[h] == height_map["average"], Or([mother_vars[hp] == mother_map["Penny"] for hp in range(h+1, 6)])))

# Clue 3
solver.add(Implies(mother_vars[1] == mother_map["Janelle"], name_vars[1] == name_map["Bob"]))
solver.add(Implies(mother_vars[2] == mother_map["Janelle"], name_vars[2] == name_map["Bob"]))
solver.add(Implies(mother_vars[3] == mother_map["Janelle"], name_vars[3] == name_map["Bob"]))
solver.add(Implies(mother_vars[4] == mother_map["Janelle"], name_vars[4] == name_map["Bob"]))
solver.add(Implies(mother_vars[5] == mother_map["Janelle"], name_vars[5] == name_map["Bob"]))

# Clue 4
solver.add(name_vars[2] != name_map["Peter"])

# Clue 5
for h in range(1, 5):
    solver.add(Implies(height_vars[h] == height_map["short"], name_vars[h+1] == name_map["Arnold"]))

# Clue 6
solver.add(Implies(height_vars[1] == height_map["very tall"], name_vars[1] == name_map["Arnold"]))
solver.add(Implies(height_vars[2] == height_map["very tall"], name_vars[2] == name_map["Arnold"]))
solver.add(Implies(height_vars[3] == height_map["very tall"], name_vars[3] == name_map["Arnold"]))
solver.add(Implies(height_vars[4] == height_map["very tall"], name_vars[4] == name_map["Arnold"]))
solver.add(Implies(height_vars[5] == height_map["very tall"], name_vars[5] == name_map["Arnold"]))

# Clue 7
for h in range(1, 5):
    solver.add(Implies(name_vars[h] == name_map["Bob"], height_vars[h+1] == height_map["average"]))

# Clue 8
solver.add(name_vars[5] != name_map["Eric"])

# Clue 9
for h in range(2, 6):
    solver.add(Implies(height_vars[h] == height_map["very tall"], Or([mother_vars[hp] == mother_map["Holly"] for hp in range(1, h)])))

# Clue 10
solver.add(Implies(name_vars[1] == name_map["Eric"], mother_vars[1] == mother_map["Kailyn"]))
solver.add(Implies(name_vars[2] == name_map["Eric"], mother_vars[2] == mother_map["Kailyn"]))
solver.add(Implies(name_vars[3] == name_map["Eric"], mother_vars[3] == mother_map["Kailyn"]))
solver.add(Implies(name_vars[4] == name_map["Eric"], mother_vars[4] == mother_map["Kailyn"]))
solver.add(Implies(name_vars[5] == name_map["Eric"], mother_vars[5] == mother_map["Kailyn"]))

# Clue 11
solver.add(height_vars[5] == height_map["very short"])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": []
        }
    }
    for h in houses:
        name_val = names[model.evaluate(name_vars[h]).as_long()]
        mother_val = mothers[model.evaluate(mother_vars[h]).as_long()]
        height_val = heights[model.evaluate(height_vars[h]).as_long()]
        solution["solution"]["rows"].append([str(h), name_val, mother_val, height_val])
    
    print(solution)
else:
    print("No solution found")