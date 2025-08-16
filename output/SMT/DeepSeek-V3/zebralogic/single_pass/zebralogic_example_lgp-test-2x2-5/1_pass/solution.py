from z3 import *

# Create the solver
s = Solver()

# Define the houses
houses = [1, 2]

# Create variables for each attribute
name = {h: String(f"name_{h}") for h in houses}
style = {h: String(f"style_{h}") for h in houses}

# Add uniqueness constraints
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([style[h] for h in houses]))

# Possible values
possible_names = ["Eric", "Arnold"]
possible_styles = ["victorian", "colonial"]

# Each attribute must be one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in possible_names]))
    s.add(Or([style[h] == st for st in possible_styles]))

# Apply the clues
# Clue 1: Victorian is left of colonial
s.add(Or(
    And(style[1] == "victorian", style[2] == "colonial")
))

# Clue 2: Eric is in the first house
s.add(name[1] == "Eric")

# Check for solution
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": []
        }
    }
    
    for h in sorted(houses):
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(style[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    
    # Convert to JSON string and print
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")