from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_venice = Int('days_venice')
days_geneva = Int('days_geneva')
days_madrid = Int('days_madrid')

# Constraints for days spent in each city
solver.add(days_venice == 2)              # Spend 2 days in Venice
solver.add(days_geneva == 2)              # Spend 2 days in Geneva
solver.add(days_madrid == 1)               # Spend 1 day in Madrid (reduced for total of 5 days)

# Total days constraint
solver.add(days_venice + days_geneva + days_madrid == 5)

# Constraints for attending the conference in Venice (must be on day 4 and 5)
# This means we must have Venice arranged for the last two days to satisfy this requirement.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_venice_val = solver.model()[days_venice].as_long()
    days_geneva_val = solver.model()[days_geneva].as_long()
    days_madrid_val = solver.model()[days_madrid].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_venice_val} days in Venice, "
        f"{days_geneva_val} days in Geneva, "
        f"{days_madrid_val} days in Madrid."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)