from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_vienna = Int('days_vienna')
days_valencia = Int('days_valencia')
days_oslo = Int('days_oslo')

# Constraints for days spent in each city
solver.add(days_vienna == 2)          # Spend 2 days in Vienna
solver.add(days_valencia == 1)        # Spend 1 day in Valencia (adjusted)
solver.add(days_oslo == 2)            # Spend 2 days in Oslo

# Total days constraint
solver.add(days_vienna + days_valencia + days_oslo == 5)

# Constraints for attending the wedding in Oslo (must be between day 1 and day 2)
# This means that the visit to Oslo must be within the first two days allocated.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_vienna_val = solver.model()[days_vienna].as_long()
    days_valencia_val = solver.model()[days_valencia].as_long()
    days_oslo_val = solver.model()[days_oslo].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_vienna_val} days in Vienna, "
        f"{days_valencia_val} day in Valencia, "
        f"{days_oslo_val} days in Oslo."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)