from z3 import *
import json

# Define the variables
names = ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold']
vacations = ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach']
houses = range(1, 7)

# Create the solver
solver = Solver()

# Create dictionaries to hold the variables
name_vars = {name: Int(name) for name in names}
vacation_vars = {vacation: Int(vacation) for vacation in vacations}

# Add constraints for unique assignments
solver.add(Distinct([name_vars[name] for name in names]))
solver.add(Distinct([vacation_vars[vacation] for vacation in vacations]))

# Add constraints for houses being between 1 and 6
for var in list(name_vars.values()) + list(vacation_vars.values()):
    solver.add(var >= 1)
    solver.add(var <= 6)

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

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution
    solution = []
    for house in houses:
        name = next(name for name, var in name_vars.items() if model.evaluate(var).as_long() == house)
        vacation = next(vacation for vacation, var in vacation_vars.items() if model.evaluate(var).as_long() == house)
        solution.append([str(house), name, vacation])
    
    # Output the solution as JSON
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": solution
        }
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found")