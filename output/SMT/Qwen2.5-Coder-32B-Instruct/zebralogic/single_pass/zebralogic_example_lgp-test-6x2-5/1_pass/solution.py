from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
names = ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold']
vacations = ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach']

# Create dictionaries to map names and vacations to Z3 variables
name_vars = {name: Int(name) for name in names}
vacation_vars = {vacation: Int(vacation) for vacation in vacations}

# Add constraints for unique positions (1 to 6)
for var_dict in [name_vars, vacation_vars]:
    solver.add(Distinct(var_dict.values()))
    for var in var_dict.values():
        solver.add(And(var >= 1, var <= 6))

# Apply the clues
# 1. The person who goes on cultural tours is somewhere to the left of the person who loves beach vacations.
solver.add(vacation_vars['cultural'] < vacation_vars['beach'])

# 2. Eric is somewhere to the right of Alice.
solver.add(name_vars['Eric'] > name_vars['Alice'])

# 3. Eric is in the second house.
solver.add(name_vars['Eric'] == 2)

# 4. The person who goes on cultural tours is in the third house.
solver.add(vacation_vars['cultural'] == 3)

# 5. Bob is directly left of Arnold.
solver.add(name_vars['Bob'] + 1 == name_vars['Arnold'])

# 6. The person who enjoys camping trips is not in the first house.
solver.add(vacation_vars['camping'] != 1)

# 7. The person who goes on cultural tours is Peter.
solver.add(name_vars['Peter'] == vacation_vars['cultural'])

# 8. The person who likes going on cruises is Bob.
solver.add(name_vars['Bob'] == vacation_vars['cruise'])

# 9. The person who prefers city breaks is in the fourth house.
solver.add(vacation_vars['city'] == 4)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Create a mapping from house number to name and vacation
    house_to_name = {model.evaluate(name_vars[name]).as_long(): name for name in names}
    house_to_vacation = {model.evaluate(vacation_vars[vacation]).as_long(): vacation for vacation in vacations}
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": []
        }
    }
    
    for house in range(1, 7):
        name = house_to_name[house]
        vacation = house_to_vacation[house]
        solution["solution"]["rows"].append([str(house), name, vacation])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")