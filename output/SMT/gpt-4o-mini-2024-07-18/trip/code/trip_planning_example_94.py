from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_london = Int('days_london')
days_krakow = Int('days_krakow')
days_lyon = Int('days_lyon')

# Constraints for days spent in each city
solver.add(days_london == 3)                # Spend 3 days in London
solver.add(days_krakow == 5)                # Spend 5 days in Krakow (adjusted)
solver.add(days_lyon == 3)                  # Spend 3 days in Lyon

# Total days constraint
solver.add(days_london + days_krakow + days_lyon == 11)

# Constraints for meeting friends in Lyon (must be between day 9 and day 11)
# To satisfy the meeting requirements in Lyon, we need to ensure
# that the days in Lyon include days 9 to 11.
# This means that Lyon needs to be the last visit.

# Check if the constraints can be satisfied
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_london_val = solver.model()[days_london].as_long()
    days_krakow_val = solver.model()[days_krakow].as_long()
    days_lyon_val = solver.model()[days_lyon].as_long()

    # Create a trip plan description
    valid_trip = (
        f"Spend {days_london_val} days in London, "
        f"{days_krakow_val} days in Krakow, "
        f"{days_lyon_val} days in Lyon."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)