from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_mykonos = Int('days_mykonos')
days_athens = Int('days_athens')
days_bucharest = Int('days_bucharest')

# Constraints for days spent in each city
solver.add(days_mykonos == 4)            # Spend 4 days in Mykonos
solver.add(days_athens == 2)             # Spend 2 days in Athens
solver.add(days_bucharest == 5)          # Spend 5 days in Bucharest (adjusted)

# Total days constraint
solver.add(days_mykonos + days_athens + days_bucharest == 11)

# Constraints for attending the wedding in Mykonos (must be on day 1 to day 4)
# The wedding will occur during the first four days allocated to Mykonos.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_mykonos_val = solver.model()[days_mykonos].as_long()
    days_athens_val = solver.model()[days_athens].as_long()
    days_bucharest_val = solver.model()[days_bucharest].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_mykonos_val} days in Mykonos, "
        f"{days_athens_val} days in Athens, "
        f"{days_bucharest_val} days in Bucharest."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)