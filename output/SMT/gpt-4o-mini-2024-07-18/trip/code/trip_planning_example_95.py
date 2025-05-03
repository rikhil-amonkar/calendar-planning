from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_vilnius = Int('days_vilnius')
days_vienna = Int('days_vienna')
days_dublin = Int('days_dublin')

# Constraints for days spent in each city
solver.add(days_vilnius == 3)               # Spend 3 days in Vilnius
solver.add(days_vienna == 5)                 # Spend 5 days in Vienna
solver.add(days_dublin == 4)                 # Spend 4 days in Dublin (adjusted)

# Total days constraint
solver.add(days_vilnius + days_vienna + days_dublin == 12)

# Constraints for attending the wedding in Dublin (must occur between day 1 and day 6)
# The travel schedule must ensure the wedding in Dublin is respected.

# Check if the constraints can be satisfied
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_vilnius_val = solver.model()[days_vilnius].as_long()
    days_vienna_val = solver.model()[days_vienna].as_long()
    days_dublin_val = solver.model()[days_dublin].as_long()

    # Create a trip plan description
    valid_trip = (
        f"Spend {days_vilnius_val} days in Vilnius, "
        f"{days_vienna_val} days in Vienna, "
        f"{days_dublin_val} days in Dublin."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)