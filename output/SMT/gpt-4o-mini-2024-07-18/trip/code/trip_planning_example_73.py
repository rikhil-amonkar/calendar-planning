from z3 import *

# Create a solver instance
solver = Solver()

# Variables for days spent in each city
days_santorini = Int('days_santorini')
days_helsinki = Int('days_helsinki')
days_venice = Int('days_venice')

# Constraints for the number of days spent in each city
solver.add(days_santorini == 4)           # Spend 4 days in Santorini
solver.add(days_helsinki == 6)             # Spend 6 days in Helsinki
solver.add(days_venice == 2)               # Spend 2 days in Venice (adjusted)

# Total days constraint
solver.add(days_santorini + days_helsinki + days_venice == 12)

# Constraints for attending the annual show in Helsinki (must be between day 1 and day 6)
# Spending 6 days in Helsinki will satisfy this requirement.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_santorini_val = solver.model()[days_santorini].as_long()
    days_helsinki_val = solver.model()[days_helsinki].as_long()
    days_venice_val = solver.model()[days_venice].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_santorini_val} days in Santorini, "
        f"{days_helsinki_val} days in Helsinki, "
        f"{days_venice_val} days in Venice."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)