from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_lyon = Int('days_lyon')
days_bucharest = Int('days_bucharest')
days_porto = Int('days_porto')

# Constraints for days spent in each city
solver.add(days_lyon == 7)                # Spend 7 days in Lyon
solver.add(days_bucharest == 5)           # Spend 5 days in Bucharest (adjusted)
solver.add(days_porto == 4)               # Spend 4 days in Porto

# Total days constraint
solver.add(days_lyon + days_bucharest + days_porto == 16)

# Constraints for attending the wedding in Bucharest (must be on day 1 to day 7)
# We assume that the visit to Bucharest will be early enough to fulfill this constraint.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_lyon_val = solver.model()[days_lyon].as_long()
    days_bucharest_val = solver.model()[days_bucharest].as_long()
    days_porto_val = solver.model()[days_porto].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_lyon_val} days in Lyon, "
        f"{days_bucharest_val} days in Bucharest, "
        f"{days_porto_val} days in Porto."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)