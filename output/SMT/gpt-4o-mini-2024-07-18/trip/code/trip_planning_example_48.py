from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_split = Int('days_split')
days_manchester = Int('days_manchester')
days_geneva = Int('days_geneva')

# Constraints for days spent in each city
solver.add(days_split == 1)             # Spend 1 day in Split
solver.add(days_manchester == 1)        # Spend 1 day in Manchester
solver.add(days_geneva == 2)            # Spend 2 days in Geneva

# Total days constraint
solver.add(days_split + days_manchester + days_geneva == 4)

# Constraints for meeting a friend in Split (must be on day 2)
# This requires day 2 to be allocated for Split.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_split_val = solver.model()[days_split].as_long()
    days_manchester_val = solver.model()[days_manchester].as_long()
    days_geneva_val = solver.model()[days_geneva].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_split_val} day in Split, "
        f"{days_manchester_val} day in Manchester, "
        f"{days_geneva_val} days in Geneva."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)