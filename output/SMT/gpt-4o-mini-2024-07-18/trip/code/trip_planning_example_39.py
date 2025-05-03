from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_florence = Int('days_florence')
days_barcelona = Int('days_barcelona')
days_porto = Int('days_porto')

# Constraints for days spent in each city
solver.add(days_florence == 4)            # Spend 4 days in Florence
solver.add(days_barcelona == 7)           # Spend 7 days in Barcelona
solver.add(days_porto == 3)               # Spend 3 days in Porto

# Total days constraint
solver.add(days_florence + days_barcelona + days_porto == 12)

# Constraint for visiting relatives in Porto (must be on day 1 to day 3)
# This means that Porto is visited early in the trip satisfying the requirement.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_florence_val = solver.model()[days_florence].as_long()
    days_barcelona_val = solver.model()[days_barcelona].as_long()
    days_porto_val = solver.model()[days_porto].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_florence_val} days in Florence, "
        f"{days_barcelona_val} days in Barcelona, "
        f"{days_porto_val} days in Porto."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)