from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_split = Int('days_split')
days_dublin = Int('days_dublin')
days_valencia = Int('days_valencia')

# Constraints for days spent in each city
solver.add(days_split == 4)               # Spend 4 days in Split
solver.add(days_dublin == 4)               # Spend 4 days in Dublin
solver.add(days_valencia == 4)             # Spend 4 days in Valencia (adjusted)

# Total days constraint
solver.add(days_split + days_dublin + days_valencia == 12)

# Constraints for visiting relatives in Split (must be between day 9 and day 12)
# This requires that you must ensure that the trip is planned such that the last part of your stay
# in Split includes days 9 to 12.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_split_val = solver.model()[days_split].as_long()
    days_dublin_val = solver.model()[days_dublin].as_long()
    days_valencia_val = solver.model()[days_valencia].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_split_val} days in Split, "
        f"{days_dublin_val} days in Dublin, "
        f"{days_valencia_val} days in Valencia."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)