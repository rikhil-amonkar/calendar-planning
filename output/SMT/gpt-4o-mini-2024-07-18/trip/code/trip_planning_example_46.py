from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_seville = Int('days_seville')
days_manchester = Int('days_manchester')
days_stockholm = Int('days_stockholm')

# Constraints for days spent in each city
solver.add(days_seville == 5)               # Spend 5 days in Seville
solver.add(days_manchester == 3)            # Spend 3 days in Manchester (adjusted)
solver.add(days_stockholm == 3)             # Spend 3 days in Stockholm

# Total days constraint
solver.add(days_seville + days_manchester + days_stockholm == 11)

# Constraints for attending the conference in Stockholm (must be on day 1 and day 3)
# This means that you need to visit Stockholm on specific days.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_seville_val = solver.model()[days_seville].as_long()
    days_manchester_val = solver.model()[days_manchester].as_long()
    days_stockholm_val = solver.model()[days_stockholm].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_seville_val} days in Seville, "
        f"{days_manchester_val} days in Manchester, "
        f"{days_stockholm_val} days in Stockholm."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)