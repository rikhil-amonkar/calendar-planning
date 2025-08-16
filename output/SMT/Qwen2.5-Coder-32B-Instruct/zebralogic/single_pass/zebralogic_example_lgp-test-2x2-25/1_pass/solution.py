from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
house_arnold = Int('house_arnold')
house_beach_lover = Int('house_beach_lover')

# Constraints
# There are only two houses
solver.add(house_arnold >= 1)
solver.add(house_arnold <= 2)
solver.add(house_beach_lover >= 1)
solver.add(house_beach_lover <= 2)

# Arnold is somewhere to the right of the person who loves beach vacations
solver.add(house_arnold > house_beach_lover)

# Each house is occupied by a different person
solver.add(house_arnold != house_beach_lover)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    house_arnold_value = model[house_arnold].as_long()
    house_beach_lover_value = model[house_beach_lover].as_long()
    
    # Determine the house and vacation for each person
    if house_arnold_value == 1:
        house_1_name = "Arnold"
        house_1_vacation = "mountain"
        house_2_name = "Eric"
        house_2_vacation = "beach"
    else:
        house_1_name = "Eric"
        house_1_vacation = "beach"
        house_2_name = "Arnold"
        house_2_vacation = "mountain"
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": [
                ["1", house_1_name, house_1_vacation],
                ["2", house_2_name, house_2_vacation]
            ]
        }
    }
    
    print(solution)
else:
    print("No solution found")