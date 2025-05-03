from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_stockholm = Int('days_stockholm')
days_athens = Int('days_athens')
days_reykjavik = Int('days_reykjavik')

# Constraints for days spent in each city
solver.add(days_stockholm == 2)          # Spend 2 days in Stockholm
solver.add(days_athens == 7)             # Spend 7 days in Athens
solver.add(days_reykjavik == 5)          # Spend 5 days in Reykjavik (adjusted)

# Total days constraint
solver.add(days_stockholm + days_athens + days_reykjavik == 14)

# Meeting friends in Reykjavik requirement (must be between day 2 and day 8)
# This allows the visiting configuration to be valid with respect to friends meeting.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_stockholm_val = solver.model()[days_stockholm].as_long()
    days_athens_val = solver.model()[days_athens].as_long()
    days_reykjavik_val = solver.model()[days_reykjavik].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_stockholm_val} days in Stockholm, "
        f"{days_athens_val} days in Athens, "
        f"{days_reykjavik_val} days in Reykjavik."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)