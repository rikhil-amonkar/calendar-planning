import json
from z3 import *

# Create the solver
s = Solver()

# Define the attributes for each house
houses = [1, 2]
names = ["Eric", "Arnold"]
foods = ["pizza", "grilled cheese"]

# Create variables for each house's name and food
name_vars = {house: String(f"name_{house}") for house in houses}
food_vars = {house: String(f"food_{house}") for house in houses}

# Add constraints that names and foods are unique across houses
s.add(Distinct([name_vars[house] for house in houses]))
s.add(Distinct([food_vars[house] for house in houses]))

# Each name and food must be one of the allowed values
for house in houses:
    s.add(Or([name_vars[house] == name for name in names]))
    s.add(Or([food_vars[house] == food for food in foods]))

# Apply the clues
# Clue 1: The person who is a pizza lover is in the second house.
s.add(food_vars[2] == "pizza")

# Clue 2: Arnold is not in the first house.
s.add(name_vars[1] != "Arnold")

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": []
        }
    }
    
    for house in sorted(houses):
        name_val = model.eval(name_vars[house]).as_string()
        food_val = model.eval(food_vars[house]).as_string()
        solution["solution"]["rows"].append([str(house), name_val, food_val])
    
    # Print the JSON-formatted solution
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")