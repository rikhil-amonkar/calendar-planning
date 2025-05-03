from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_stuttgart = Int('days_stuttgart')
days_vienna = Int('days_vienna')
days_oslo = Int('days_oslo')

# Constraints for days spent in each city
solver.add(days_stuttgart == 6)           # Spend 6 days in Stuttgart
solver.add(days_vienna == 4)              # Spend 4 days in Vienna (adjusted)
solver.add(days_oslo == 2)                # Spend 2 days in Oslo (adjusted)

# Total days constraint
solver.add(days_stuttgart + days_vienna + days_oslo == 12)

# Constraints for visiting relatives in Oslo (must be between day 1 and day 3)
# This means that you need to visit Oslo within those days.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_stuttgart_val = solver.model()[days_stuttgart].as_long()
    days_vienna_val = solver.model()[days_vienna].as_long()
    days_oslo_val = solver.model()[days_oslo].as_long()

    # Create a trip plan description
    valid_trip = (
        f"Spend {days_stuttgart_val} days in Stuttgart, "
        f"{days_vienna_val} days in Vienna, "
        f"{days_oslo_val} days in Oslo."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)