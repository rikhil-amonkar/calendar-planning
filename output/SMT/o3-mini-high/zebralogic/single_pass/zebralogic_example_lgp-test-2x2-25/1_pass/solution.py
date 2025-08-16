from z3 import Solver, Int, Or, sat
import json

# Create the Z3 solver instance.
solver = Solver()

# Define integer variables for the positions (houses 1 and 2)
Arnold = Int("Arnold")
Eric = Int("Eric")
beach = Int("beach")
mountain = Int("mountain")

# Each variable must be either 1 or 2.
solver.add(Or(Arnold == 1, Arnold == 2))
solver.add(Or(Eric == 1, Eric == 2))
solver.add(Or(beach == 1, beach == 2))
solver.add(Or(mountain == 1, mountain == 2))

# Each person is in a unique house.
solver.add(Arnold != Eric)
# Each vacation preference is unique.
solver.add(beach != mountain)

# Clue: "Arnold is somewhere to the right of the person who loves beach vacations."
solver.add(Arnold > beach)

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    # Prepare the solution rows for houses 1 and 2.
    rows = []
    for house in [1, 2]:
        # Determine the name for the house.
        if model.evaluate(Arnold).as_long() == house:
            name = "Arnold"
        elif model.evaluate(Eric).as_long() == house:
            name = "Eric"
        else:
            name = None
        
        # Determine the vacation for the house.
        if model.evaluate(beach).as_long() == house:
            vacation = "beach"
        elif model.evaluate(mountain).as_long() == house:
            vacation = "mountain"
        else:
            vacation = None
        
        rows.append([str(house), name, vacation])
    
    # Create the JSON result.
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": rows
        }
    }
    # Output the JSON formatted result.
    print(json.dumps(result, indent=2))
else:
    print("No solution found")