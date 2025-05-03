from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_prague = Int('days_prague')
days_vienna = Int('days_vienna')
days_porto = Int('days_porto')

# Constraints for days spent in each city
solver.add(days_prague == 3)            # Spend 3 days in Prague
solver.add(days_vienna == 3)             # Spend 3 days in Vienna
solver.add(days_porto == 5)              # Spend 5 days in Porto

# Total days constraint
solver.add(days_prague + days_vienna + days_porto == 9)

# Constraints for the workshop in Prague (must occur between day 1 and 3)
# Given you have 3 days in Prague, you will be there from days 1 to 3.
# Since you will be in Prague for the last day of your visit to the workshop,
# the 3 days in Prague fits well within this requirement.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_prague_val = solver.model()[days_prague].as_long()
    days_vienna_val = solver.model()[days_vienna].as_long()
    days_porto_val = solver.model()[days_porto].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_prague_val} days in Prague, "
        f"{days_vienna_val} days in Vienna, "
        f"{days_porto_val} days in Porto."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)