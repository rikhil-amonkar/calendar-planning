import json
from z3 import *

solver = Solver()

# Variables for house 1
name1 = String('name1')
food1 = String('food1')
mother1 = String('mother1')

# Variables for house 2
name2 = String('name2')
food2 = String('food2')
mother2 = String('mother2')

# Add constraints for unique attributes
# Names
solver.add(Or(name1 == "Arnold", name1 == "Eric"))
solver.add(Or(name2 == "Arnold", name2 == "Eric"))
solver.add(name1 != name2)

# Foods
solver.add(Or(food1 == "grilled cheese", food1 == "pizza"))
solver.add(Or(food2 == "grilled cheese", food2 == "pizza"))
solver.add(food1 != food2)

# Mothers
solver.add(Or(mother1 == "Holly", mother1 == "Aniya"))
solver.add(Or(mother2 == "Holly", mother2 == "Aniya"))
solver.add(mother1 != mother2)

# Clue 1: grilled cheese is directly left of pizza → house1 has grilled cheese, house2 pizza
solver.add(food1 == "grilled cheese")
solver.add(food2 == "pizza")

# Clue 2: Arnold not in house 2 → name1 is Arnold
solver.add(name1 == "Arnold")

# Clue 3: Arnold's mother is Holly
solver.add(mother1 == "Holly")

if solver.check() == sat:
    model = solver.model()
    # Extract values
    n1 = model[name1]
    f1 = model[food1]
    m1 = model[mother1]
    n2 = model[name2]
    f2 = model[food2]
    m2 = model[mother2]
    
    # Construct the solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": [
                ["1", n1, f1, m1],
                ["2", n2, f2, m2]
            ]
        }
    }
    
    # Print as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")