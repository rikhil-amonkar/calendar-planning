from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_valencia = Int('days_valencia')
days_split = Int('days_split')
days_lyon = Int('days_lyon')

# Constraints for days spent in each city
solver.add(days_valencia == 5)            # Spend 5 days in Valencia
solver.add(days_split == 7)               # Spend 7 days in Split
solver.add(days_lyon == 6)                 # Spend 6 days in Lyon

# Total days constraint
solver.add(days_valencia + days_split + days_lyon == 16)

# Constraints for the annual show in Split (must be attended from day 10 to 16)
# Given you are spending 7 days in Split, you can set your schedule to 
# accommodate being there from day 10 onward.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_valencia_val = solver.model()[days_valencia].as_long()
    days_split_val = solver.model()[days_split].as_long()
    days_lyon_val = solver.model()[days_lyon].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_valencia_val} days in Valencia, "
        f"{days_split_val} days in Split, "
        f"{days_lyon_val} days in Lyon."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)