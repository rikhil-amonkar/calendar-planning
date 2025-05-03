from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_reykjavik = Int('days_reykjavik')
days_milan = Int('days_milan')
days_split = Int('days_split')

# Constraints for days spent in each city
solver.add(days_reykjavik == 5)          # Spend 5 days in Reykjavik
solver.add(days_milan == 7)               # Spend 7 days in Milan
solver.add(days_split == 3)               # Spend 3 days in Split

# Total days constraint
solver.add(days_reykjavik + days_milan + days_split == 13)

# Constraints for visiting relatives in Split (must be between day 1 and day 3)
# This means that the stay in Split is during the first three days.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_reykjavik_val = solver.model()[days_reykjavik].as_long()
    days_milan_val = solver.model()[days_milan].as_long()
    days_split_val = solver.model()[days_split].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_reykjavik_val} days in Reykjavik, "
        f"{days_milan_val} days in Milan, "
        f"{days_split_val} days in Split."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)