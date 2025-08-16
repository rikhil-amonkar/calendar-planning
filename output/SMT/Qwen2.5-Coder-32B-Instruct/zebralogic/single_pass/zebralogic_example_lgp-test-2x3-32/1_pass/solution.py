from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
names = ['Eric', 'Arnold']
months = ['sept', 'april']
colors = ['yellow', 'red']

# Create symbolic variables for each house
house1_name = String('house1_name')
house1_month = String('house1_month')
house1_color = String('house1_color')

house2_name = String('house2_name')
house2_month = String('house2_month')
house2_color = String('house2_color')

# Add constraints for names, months, and colors
solver.add(house1_name != house2_name)
solver.add(house1_month != house2_month)
solver.add(house1_color != house2_color)

# Add domain constraints
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house1_month == 'sept', house1_month == 'april'))
solver.add(Or(house1_color == 'yellow', house1_color == 'red'))

solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))
solver.add(Or(house2_month == 'sept', house2_month == 'april'))
solver.add(Or(house2_color == 'yellow', house2_color == 'red'))

# Add problem-specific constraints
# 1. Eric is the person who loves yellow.
solver.add(Implies(house1_color == 'yellow', house1_name == 'Eric'))
solver.add(Implies(house2_color == 'yellow', house2_name == 'Eric'))

# 2. The person whose birthday is in April is in the first house.
solver.add(house1_month == 'april')

# 3. The person who loves yellow is not in the first house.
solver.add(house1_color != 'yellow')

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Extract the solution
    house1_solution = [model[house1_name], model[house1_month], model[house1_color]]
    house2_solution = [model[house2_name], model[house2_month], model[house2_color]]

    # Format the solution as required
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": [
                ["1", str(house1_solution[0]), str(house1_solution[1]), str(house1_solution[2])],
                ["2", str(house2_solution[0]), str(house2_solution[1]), str(house2_solution[2])]
            ]
        }
    }

    print(solution)
else:
    print("No solution found")