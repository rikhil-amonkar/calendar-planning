from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_santorini = Int('days_santorini')
days_amsterdam = Int('days_amsterdam')
days_istanbul = Int('days_istanbul')

# Constraints for days spent in each city
solver.add(days_santorini == 3)        # Spend 3 days in Santorini
solver.add(days_amsterdam == 7)        # Spend 7 days in Amsterdam
solver.add(days_istanbul == 6)         # Spend 6 days in Istanbul

# Total days constraint
solver.add(days_santorini + days_amsterdam + days_istanbul == 14)

# Constraints for visiting relatives in Santorini (must be between day 12 and 14)
# This means that the trip must be arranged so that you arrive in Santorini
# by day 12, leaving enough days before day 12 to fit in stays in Amsterdam
# and Istanbul.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_santorini_val = solver.model()[days_santorini].as_long()
    days_amsterdam_val = solver.model()[days_amsterdam].as_long()
    days_istanbul_val = solver.model()[days_istanbul].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_santorini_val} days in Santorini, "
        f"{days_amsterdam_val} days in Amsterdam, "
        f"{days_istanbul_val} days in Istanbul."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)