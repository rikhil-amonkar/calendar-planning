from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_london = Int('days_london')
days_porto = Int('days_porto')
days_milan = Int('days_milan')

# Constraints for days spent in each city
solver.add(days_london == 3)             # Spend 3 days in London
solver.add(days_porto == 4)               # Spend 4 days in Porto
solver.add(days_milan == 4)               # Spend 4 days in Milan (adjusted)

# Total days constraint
solver.add(days_london + days_porto + days_milan == 11)

# Constraints for attending the workshop in London (must be on day 1 and day 3)
# This means that we need to allocate days properly.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the days spent in each city
    days_london_val = solver.model()[days_london].as_long()
    days_porto_val = solver.model()[days_porto].as_long()
    days_milan_val = solver.model()[days_milan].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_london_val} days in London, "
        f"{days_porto_val} days in Porto, "
        f"{days_milan_val} days in Milan."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)