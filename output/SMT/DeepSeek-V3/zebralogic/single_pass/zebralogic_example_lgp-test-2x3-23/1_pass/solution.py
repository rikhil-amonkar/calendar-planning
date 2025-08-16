import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2]

# Define the attributes
names = ['Eric', 'Arnold']
children = ['Bella', 'Fred']
foods = ['grilled cheese', 'pizza']

# Create variables for each attribute in each house
name_vars = {house: String(f'name_{house}') for house in houses}
child_vars = {house: String(f'child_{house}') for house in houses}
food_vars = {house: String(f'food_{house}') for house in houses}

# Add constraints for uniqueness of each attribute
s.add(Distinct([name_vars[house] for house in houses]))
s.add(Distinct([child_vars[house] for house in houses]))
s.add(Distinct([food_vars[house] for house in houses]))

# Each attribute must be one of the allowed values
for house in houses:
    s.add(Or([name_vars[house] == name for name in names]))
    s.add(Or([child_vars[house] == child for child in children]))
    s.add(Or([food_vars[house] == food for food in foods]))

# Apply clue 1: The person who is a pizza lover is Arnold.
for house in houses:
    s.add(Implies(food_vars[house] == 'pizza', name_vars[house] == 'Arnold'))

# Apply clue 2: The person who loves eating grilled cheese is directly left of the person's child is named Fred.
# This means house 1 has grilled cheese and house 2's child is Fred
s.add(Or(
    And(food_vars[1] == 'grilled cheese', child_vars[2] == 'Fred'),
    And(food_vars[2] == 'grilled cheese', child_vars[1] == 'Fred')  # Not possible since house 2 can't be left of house 1
))
# Since house 2 cannot be to the left of house 1, the only possibility is house 1 has grilled cheese and house 2 has child Fred
s.add(food_vars[1] == 'grilled cheese')
s.add(child_vars[2] == 'Fred')

# Check for a solution
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": []
        }
    }
    
    for house in sorted(houses):
        name = model.eval(name_vars[house]).as_string()
        child = model.eval(child_vars[house]).as_string()
        food = model.eval(food_vars[house]).as_string()
        solution["solution"]["rows"].append([str(house), name, child, food])
    
    # Output the solution as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")