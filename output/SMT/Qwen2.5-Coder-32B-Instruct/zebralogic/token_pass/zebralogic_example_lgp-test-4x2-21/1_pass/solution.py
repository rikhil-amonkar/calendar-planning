from z3 import *

# Define the solver
solver = Solver()

# Define the variables for names and house styles
names = ["Eric", "Arnold", "Alice", "Peter"]
house_styles = ["craftsman", "colonial", "ranch", "victorian"]

# Create arrays for names and house styles for each house
name_vars = [String(f"name_{i}") for i in range(4)]
house_style_vars = [String(f"house_style_{i}") for i in range(4)]

# Add constraints for uniqueness of names and house styles
solver.add(Distinct(name_vars))
solver.add(Distinct(house_style_vars))

# Apply the clues
# Clue 1: Alice is in the second house
solver.add(name_vars[1] == "Alice")

# Clue 2: The person residing in a Victorian house is directly left of Peter
for i in range(3):  # Only check up to the third house
    solver.add(Implies(house_style_vars[i] == "victorian", name_vars[i + 1] == "Peter"))

# Clue 3: Peter is somewhere to the right of the person in a ranch-style home
for i in range(3):  # Only check up to the third house
    for j in range(i + 1, 4):
        solver.add(Implies(house_style_vars[i] == "ranch", name_vars[j] == "Peter"))

# Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house
for i in range(3):  # Only check up to the third house
    for j in range(i + 1, 4):
        solver.add(Implies(house_style_vars[i] == "craftsman", name_vars[j] == "Arnold"))

# Clue 5: The person in a Craftsman-style house is Alice
for i in range(4):
    solver.add(Implies(house_style_vars[i] == "craftsman", name_vars[i] == "Alice"))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(4):
        name_val = model[name_vars[i]].as_string()[1:-1]  # Remove quotes
        house_style_val = model[house_style_vars[i]].as_string()[1:-1]  # Remove quotes
        solution.append([str(i + 1), name_val, house_style_val])
    
    # Format the solution as JSON
    json_solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": solution
        }
    }
    print(json_solution)
else:
    print("No solution found")