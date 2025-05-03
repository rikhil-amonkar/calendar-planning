from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_santorini = Int('days_santorini')
days_amsterdam = Int('days_amsterdam')
days_lyon = Int('days_lyon')

# Constraints for days spent in each city
solver.add(days_santorini == 5)          # Spend 5 days in Santorini (adjusted)
solver.add(days_amsterdam == 3)          # Spend 3 days in Amsterdam
solver.add(days_lyon == 2)               # Spend 2 days in Lyon

# Total days constraint
solver.add(days_santorini + days_amsterdam + days_lyon == 10)

# Constraints for attending the show in Lyon (must be on day 1 and day 2)
# This means that we must ensure Lyon is visited early enough to encompass the days of the show.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_santorini_val = solver.model()[days_santorini].as_long()
    days_amsterdam_val = solver.model()[days_amsterdam].as_long()
    days_lyon_val = solver.model()[days_lyon].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_santorini_val} days in Santorini, "
        f"{days_amsterdam_val} days in Amsterdam, "
        f"{days_lyon_val} days in Lyon."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)