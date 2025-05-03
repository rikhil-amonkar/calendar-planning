from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_zurich = Int('days_zurich')
days_reykjavik = Int('days_reykjavik')
days_porto = Int('days_porto')

# Constraints for days spent in each city
solver.add(days_zurich == 6)             # Spend 6 days in Zurich
solver.add(days_reykjavik == 3)          # Spend 3 days in Reykjavik
solver.add(days_porto == 5)              # Spend 5 days in Porto (adjusted)

# Total days constraint
solver.add(days_zurich + days_reykjavik + days_porto == 14)

# Constraints for attending the workshop in Porto (must be between day 8 and day 14)
# If you spend 5 days in Porto, the 8th day can be the start of your workshop.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_zurich_val = solver.model()[days_zurich].as_long()
    days_reykjavik_val = solver.model()[days_reykjavik].as_long()
    days_porto_val = solver.model()[days_porto].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_zurich_val} days in Zurich, "
        f"{days_reykjavik_val} days in Reykjavik, "
        f"{days_porto_val} days in Porto."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)