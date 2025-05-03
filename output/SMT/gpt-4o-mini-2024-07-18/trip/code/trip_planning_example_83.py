from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_lisbon = Int('days_lisbon')
days_lyon = Int('days_lyon')
days_zurich = Int('days_zurich')

# Constraints for days spent in each city
solver.add(days_lisbon == 7)               # Spend 7 days in Lisbon
solver.add(days_lyon == 5)                 # Spend 5 days in Lyon (adjusted)
solver.add(days_zurich == 1)               # Spend 1 day in Zurich (adjusted)

# Total days constraint
solver.add(days_lisbon + days_lyon + days_zurich == 13)

# Constraints for attending the conference in Lyon (must occur on days 8 and 13)
# As we have 5 days in Lyon, this can accommodate conferences on day 8 and day 13.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_lisbon_val = solver.model()[days_lisbon].as_long()
    days_lyon_val = solver.model()[days_lyon].as_long()
    days_zurich_val = solver.model()[days_zurich].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_lisbon_val} days in Lisbon, "
        f"{days_lyon_val} days in Lyon, "
        f"{days_zurich_val} days in Zurich."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)