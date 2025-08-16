from z3 import *
import json

# Create integer variables for each person representing their house number (1 to 4)
xArnold = Int('xArnold')
xPeter = Int('xPeter')
xEric = Int('xEric')
xAlice = Int('xAlice')

# Create integer variables for each house style representing its house number (1 to 4)
yvictorian = Int('yvictorian')
yranch = Int('yranch')
ycraftsman = Int('ycraftsman')
ycolonial = Int('ycolonial')

# Initialize the solver
solver = Solver()

# Add domain constraints for persons and house styles (houses are numbered 1 to 4)
persons = [xArnold, xPeter, xEric, xAlice]
styles = [yvictorian, yranch, ycraftsman, ycolonial]

for var in persons + styles:
    solver.add(var >= 1, var <= 4)

# All persons must be in distinct houses and all styles in distinct houses
solver.add(Distinct(xArnold, xPeter, xEric, xAlice))
solver.add(Distinct(yvictorian, yranch, ycraftsman, ycolonial))

# Clue 1: Eric is the person in a Craftsman-style house
solver.add(xEric == ycraftsman)

# Clue 2: The person in a ranch-style home is directly left of the person residing in a Victorian house
solver.add(yvictorian == yranch + 1)

# Clue 3: Eric is in the third house
solver.add(xEric == 3)

# Clue 4: Arnold is in the fourth house
solver.add(xArnold == 4)

# Clue 5: The person residing in a Victorian house is Alice
solver.add(xAlice == yvictorian)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Build a mapping for houses from 1 to 4
    houses = {
        i: {"Name": None, "HouseStyle": None} for i in range(1, 5)
    }
    
    # Assign names to houses based on model values
    houses[model[xArnold].as_long()]["Name"] = "Arnold"
    houses[model[xPeter].as_long()]["Name"] = "Peter"
    houses[model[xEric].as_long()]["Name"] = "Eric"
    houses[model[xAlice].as_long()]["Name"] = "Alice"
    
    # Assign house styles to houses based on model values
    houses[model[yvictorian].as_long()]["HouseStyle"] = "victorian"
    houses[model[yranch].as_long()]["HouseStyle"] = "ranch"
    houses[model[ycraftsman].as_long()]["HouseStyle"] = "craftsman"
    houses[model[ycolonial].as_long()]["HouseStyle"] = "colonial"
    
    # Build the rows in the order of houses 1 to 4, formatting house number as string
    rows = []
    for i in sorted(houses.keys()):
        row = [str(i), houses[i]["Name"], houses[i]["HouseStyle"]]
        rows.append(row)
    
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    
    # Print the JSON solution (ensuring valid JSON format)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")