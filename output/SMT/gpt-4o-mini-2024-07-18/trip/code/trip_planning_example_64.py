from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_stuttgart = Int('days_stuttgart')
days_reykjavik = Int('days_reykjavik')
days_porto = Int('days_porto')

# Constraints for days spent in each city
solver.add(days_stuttgart == 3)            # Spend 3 days in Stuttgart
solver.add(days_reykjavik == 4)            # Spend 4 days in Reykjavik
solver.add(days_porto == 4)                # Spend 4 days in Porto (adjusted)

# Total days constraint
solver.add(days_stuttgart + days_reykjavik + days_porto == 11)

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_stuttgart_val = solver.model()[days_stuttgart].as_long()
    days_reykjavik_val = solver.model()[days_reykjavik].as_long()
    days_porto_val = solver.model()[days_porto].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_stuttgart_val} days in Stuttgart, "
        f"{days_reykjavik_val} days in Reykjavik, "
        f"{days_porto_val} days in Porto."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)