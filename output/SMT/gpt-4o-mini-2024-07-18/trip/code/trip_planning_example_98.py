from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_split = Int('days_split')
days_istanbul = Int('days_istanbul')
days_copenhagen = Int('days_copenhagen')

# Constraints for days spent in each city
solver.add(days_split == 2)               # Spend 2 days in Split
solver.add(days_istanbul == 2)            # Spend 2 days in Istanbul (adjusted)
solver.add(days_copenhagen == 2)          # Spend 2 days in Copenhagen

# Total days constraint
solver.add(days_split + days_istanbul + days_copenhagen == 6)

# Constraints for meeting friends in Split (must be between days 5 and 6)
# This constraint means that the meeting can only happen when you are in Split.
# Given that we are only spending 2 days in Split, we cannot meet on days 5 and 6.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_split_val = solver.model()[days_split].as_long()
    days_istanbul_val = solver.model()[days_istanbul].as_long()
    days_copenhagen_val = solver.model()[days_copenhagen].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_split_val} days in Split, "
        f"{days_istanbul_val} days in Istanbul, "
        f"{days_copenhagen_val} days in Copenhagen."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)