from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_venice = Int('days_venice')
days_florence = Int('days_florence')
days_zurich = Int('days_zurich')

# Constraints for days spent in each city
solver.add(days_venice == 6)             # Spend 6 days in Venice
solver.add(days_florence == 6)           # Spend 6 days in Florence
solver.add(days_zurich == 2)             # Spend 2 days in Zurich

# Total days constraint
solver.add(days_venice + days_florence + days_zurich == 12)

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_venice_val = solver.model()[days_venice].as_long()
    days_florence_val = solver.model()[days_florence].as_long()
    days_zurich_val = solver.model()[days_zurich].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_venice_val} days in Venice, "
        f"{days_florence_val} days in Florence, "
        f"{days_zurich_val} days in Zurich."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)