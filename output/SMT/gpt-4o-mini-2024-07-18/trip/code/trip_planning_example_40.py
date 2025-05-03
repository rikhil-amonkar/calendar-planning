from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_oslo = Int('days_oslo')
days_reykjavik = Int('days_reykjavik')
days_manchester = Int('days_manchester')

# Constraints for days spent in each city
solver.add(days_oslo == 6)                # Spend 6 days in Oslo
solver.add(days_reykjavik == 2)           # Spend 2 days in Reykjavik
solver.add(days_manchester == 2)          # Spend 2 days in Manchester

# Total days constraint
solver.add(days_oslo + days_reykjavik + days_manchester == 8)

# Constraints for attending the wedding in Manchester (must be on day 1 and day 2)
# This means you have to be in Manchester during the first two days.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_oslo_val = solver.model()[days_oslo].as_long()
    days_reykjavik_val = solver.model()[days_reykjavik].as_long()
    days_manchester_val = solver.model()[days_manchester].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_oslo_val} days in Oslo, "
        f"{days_reykjavik_val} days in Reykjavik, "
        f"{days_manchester_val} days in Manchester."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)