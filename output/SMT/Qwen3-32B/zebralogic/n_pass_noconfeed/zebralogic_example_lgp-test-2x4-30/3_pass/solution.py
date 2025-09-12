from z3 import *
import json

# Initialize Z3 solver
solver = Solver()

# Define variables for House 1
name1 = String('name1')
hair1 = String('hair1')
sport1 = String('sport1')
smoothie1 = String('smoothie1')

# Define variables for House 2
name2 = String('name2')
hair2 = String('hair2')
sport2 = String('sport2')
smoothie2 = String('smoothie2')

# Add constraints (example constraints; replace with actual problem logic)
# Example: All values must be unique per attribute
solver.add(Distinct(name1, name2))
solver.add(Distinct(hair1, hair2))
solver.add(Distinct(sport1, sport2))
solver.add(Distinct(smoothie1, smoothie2))

# Add additional constraints specific to the problem (e.g., from the original logic)
# Example: If "Alice" has "Blonde" hair, etc.
# Replace these with actual constraints from the original problem
solver.add(name1 == "Alice")
solver.add(hair1 == "Blonde")
solver.add(sport1 == "Tennis")
solver.add(smoothie1 == "Strawberry")

# Check for solution
if solver.check() == sat:
    model = solver.model()
    # Extract values for house 1 and 2
    n1 = str(model[name1])
    h1 = str(model[hair1])
    s1 = str(model[sport1])
    sm1 = str(model[smoothie1])

    n2 = str(model[name2])
    h2 = str(model[hair2])
    s2 = str(model[sport2])
    sm2 = str(model[smoothie2])

    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": [
                ["1", n1, h1, s1, sm1],
                ["2", n2, h2, s2, sm2]
            ]
        }
    }

    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"error": "No solution found"}, indent=2))