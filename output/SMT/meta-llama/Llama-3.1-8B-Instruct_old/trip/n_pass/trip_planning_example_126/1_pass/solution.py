from z3 import *

# Define the days as integers
days = Int('days')

# Define the variables for each city
krakow = Int('krakow')
paris = Int('paris')
seville = Int('seville')

# Define the constraints for each city
constraints = [
    # Krakow: 5 days in total, 1 day for the workshop
    And(krakow >= 5, krakow == 5),
    # Paris: 2 days in total
    And(paris >= 2, paris <= 2),
    # Seville: 6 days in total
    And(seville >= 6, seville <= 6),
    # Total days: 11 days
    And(krakow + paris + seville == 11),
    # Krakow to Paris: at most 1 day in between
    And(krakow + paris >= 1),
    # Paris to Seville: at most 1 day in between
    And(paris + seville >= 1),
    # Krakow to Seville: at least 1 day in between
    And(krakow + seville >= 2),
    # Ensure workshop in Krakow is between day 1 and day 5
    And(krakow >= 1, krakow <= 5)
]

# Solve the constraints
solver = Solver()
for constraint in constraints:
    solver.add(constraint)

if solver.check() == sat:
    model = solver.model()
    print(f"Krakow: {model[krakow].as_long()} days")
    print(f"Paris: {model[paris].as_long()} days")
    print(f"Seville: {model[seville].as_long()} days")
else:
    print("No solution found")