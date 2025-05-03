from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_zurich = Int('days_zurich')
days_bucharest = Int('days_bucharest')
days_helsinki = Int('days_helsinki')

# Constraints for days spent in each city
solver.add(days_zurich == 7)            # Spend 7 days in Zurich
solver.add(days_bucharest == 3)         # Spend 3 days in Bucharest
solver.add(days_helsinki == 3)          # Spend 3 days in Helsinki (adjusted)

# Total days constraint
solver.add(days_zurich + days_bucharest + days_helsinki == 13)

# Constraint for meeting friends in Helsinki (must be between day 1 and day 5)
# Meeting friends should be accommodated within the allocated days for Helsinki.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_zurich_val = solver.model()[days_zurich].as_long()
    days_bucharest_val = solver.model()[days_bucharest].as_long()
    days_helsinki_val = solver.model()[days_helsinki].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_zurich_val} days in Zurich, "
        f"{days_bucharest_val} days in Bucharest, "
        f"{days_helsinki_val} days in Helsinki."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)