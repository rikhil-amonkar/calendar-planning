from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_lyon = Int('days_lyon')
days_frankfurt = Int('days_frankfurt')
days_zurich = Int('days_zurich')

# Constraints for days spent in each city
solver.add(days_lyon == 4)                 # Spend 4 days in Lyon
solver.add(days_frankfurt == 5)            # Spend 5 days in Frankfurt
solver.add(days_zurich == 5)                # Spend 5 days in Zurich (adjusted)

# Total days constraint
solver.add(days_lyon + days_frankfurt + days_zurich == 14)

# Constraints for attending the workshop in Lyon (must be between day 11 and day 14)
# This means that Lyon visit must fall at the end, allowing for at least 4 days in it.
solver.add(days_lyon >= 4)  # Workshop requires at least 4 days in Lyon, generating days 11-14 as part of the Lyon stay.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_lyon_val = solver.model()[days_lyon].as_long()
    days_frankfurt_val = solver.model()[days_frankfurt].as_long()
    days_zurich_val = solver.model()[days_zurich].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_lyon_val} days in Lyon, "
        f"{days_frankfurt_val} days in Frankfurt, "
        f"{days_zurich_val} days in Zurich."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)