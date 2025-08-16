from z3 import *
import json

# Initialize the solver
s = Solver()

# Define string variables for names and foods of the two houses
name1 = String('name1')  # House 1 name
name2 = String('name2')  # House 2 name
food1 = String('food1')  # House 1 food
food2 = String('food2')  # House 2 food

# Constraints for names: each must be either "Eric" or "Arnold" and distinct
s.add(Or(name1 == "Eric", name1 == "Arnold"))
s.add(Or(name2 == "Eric", name2 == "Arnold"))
s.add(name1 != name2)

# Constraints for foods: each must be either "pizza" or "grilled cheese" and distinct
s.add(Or(food1 == "pizza", food1 == "grilled cheese"))
s.add(Or(food2 == "pizza", food2 == "grilled cheese"))
s.add(food1 != food2)

# Clue 1: Pizza lover is in the second house
s.add(food2 == "pizza")

# Clue 2: Arnold is not in the first house
s.add(name1 != "Arnold")

# Check for a solution
if s.check() == sat:
    m = s.model()
    # Extract the values as strings
    n1 = m[name1].as_string()
    n2 = m[name2].as_string()
    f1 = m[food1].as_string()
    f2 = m[food2].as_string()
    
    # Build the result dictionary
    result = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": [
                ["1", n1, f1],
                ["2", n2, f2]
            ]
        }
    }
    print(json.dumps(result))
else:
    print(json.dumps({"error": "No solution found"}))