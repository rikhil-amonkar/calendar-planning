from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_frankfurt = Int('days_frankfurt')
days_reykjavik = Int('days_reykjavik')
days_split = Int('days_split')

# Constraints for days spent in each city
solver.add(days_frankfurt == 2)          # Spend 2 days in Frankfurt
solver.add(days_reykjavik == 3)           # Spend 3 days in Reykjavik
solver.add(days_split == 7)               # Spend 7 days in Split

# Total days constraint
solver.add(days_frankfurt + days_reykjavik + days_split == 10)

# Constraints for attending the workshop in Reykjavik (must be between day 8 and day 10)
# This means you should plan your Reykjavik days such that they overlap
# with day 8 to day 10.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_frankfurt_val = solver.model()[days_frankfurt].as_long()
    days_reykjavik_val = solver.model()[days_reykjavik].as_long()
    days_split_val = solver.model()[days_split].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_frankfurt_val} days in Frankfurt, "
        f"{days_reykjavik_val} days in Reykjavik, "
        f"{days_split_val} days in Split."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)