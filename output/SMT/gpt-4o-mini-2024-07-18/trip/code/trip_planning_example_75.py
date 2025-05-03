from z3 import *

# Create a solver instance
solver = Solver()

# Variables for days spent in each city
days_valencia = Int('days_valencia')
days_prague = Int('days_prague')
days_tallinn = Int('days_tallinn')

# Constraints for days spent in each city
solver.add(days_valencia == 7)             # Spend 7 days in Valencia
solver.add(days_prague == 5)                # Spend 5 days in Prague (adjusted)
solver.add(days_tallinn == 5)               # Spend 5 days in Tallinn

# Total days constraint
solver.add(days_valencia + days_prague + days_tallinn == 17)

# Constraints for the show in Valencia (must occur between days 11 and 17)
# This means that you will need to ensure Valencia is visited last so that days 11-17 are in Valencia.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_valencia_val = solver.model()[days_valencia].as_long()
    days_prague_val = solver.model()[days_prague].as_long()
    days_tallinn_val = solver.model()[days_tallinn].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_valencia_val} days in Valencia, "
        f"{days_prague_val} days in Prague, "
        f"{days_tallinn_val} days in Tallinn."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)