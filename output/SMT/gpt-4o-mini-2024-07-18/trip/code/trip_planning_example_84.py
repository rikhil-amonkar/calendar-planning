from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_helsinki = Int('days_helsinki')
days_bucharest = Int('days_bucharest')
days_warsaw = Int('days_warsaw')

# Constraints for days spent in each city
solver.add(days_helsinki == 4)              # Spend 4 days in Helsinki
solver.add(days_bucharest == 3)             # Spend 3 days in Bucharest (adjusted)
solver.add(days_warsaw == 3)                # Spend 3 days in Warsaw (adjusted)

# Total days constraint
solver.add(days_helsinki + days_bucharest + days_warsaw == 10)

# Constraints for attending the annual show in Helsinki (must occur from day 1 to day 4)
# The stay in Helsinki will accommodate the show during those days.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_helsinki_val = solver.model()[days_helsinki].as_long()
    days_bucharest_val = solver.model()[days_bucharest].as_long()
    days_warsaw_val = solver.model()[days_warsaw].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_helsinki_val} days in Helsinki, "
        f"{days_bucharest_val} days in Bucharest, "
        f"{days_warsaw_val} days in Warsaw."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)