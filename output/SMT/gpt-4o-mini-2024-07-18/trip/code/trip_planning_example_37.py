from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_reykjavik = Int('days_reykjavik')
days_porto = Int('days_porto')
days_milan = Int('days_milan')

# Constraints for days spent in each city
solver.add(days_reykjavik == 6)        # Spend 6 days in Reykjavik
solver.add(days_porto == 2)             # Spend 2 days in Porto
solver.add(days_milan == 4)             # Spend 4 days in Milan

# Total days constraint
solver.add(days_reykjavik + days_porto + days_milan == 10)

# Constraints for attending the annual show in Porto (must be on day 9 and 10)
# This means you have to visit Porto on the last two days of your trip.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_reykjavik_val = solver.model()[days_reykjavik].as_long()
    days_porto_val = solver.model()[days_porto].as_long()
    days_milan_val = solver.model()[days_milan].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_reykjavik_val} days in Reykjavik, "
        f"{days_porto_val} days in Porto, "
        f"{days_milan_val} days in Milan."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)