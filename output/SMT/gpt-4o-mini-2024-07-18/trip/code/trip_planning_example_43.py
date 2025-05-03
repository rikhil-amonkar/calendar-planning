from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_venice = Int('days_venice')
days_porto = Int('days_porto')
days_dublin = Int('days_dublin')

# Constraints for days spent in each city
solver.add(days_venice == 4)             # Spend 4 days in Venice
solver.add(days_porto == 4)               # Spend 4 days in Porto
solver.add(days_dublin == 2)              # Spend 2 days in Dublin (adjusted)

# Total days constraint
solver.add(days_venice + days_porto + days_dublin == 10)

# Constraint for meeting friends in Venice (must be between day 1 to day 4)
# This means we must ensure that the visit to Venice covers day 1 to day 4.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_venice_val = solver.model()[days_venice].as_long()
    days_porto_val = solver.model()[days_porto].as_long()
    days_dublin_val = solver.model()[days_dublin].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_venice_val} days in Venice, "
        f"{days_porto_val} days in Porto, "
        f"{days_dublin_val} days in Dublin."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)