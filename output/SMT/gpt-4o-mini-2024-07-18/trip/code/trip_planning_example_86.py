from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_brussels = Int('days_brussels')
days_krakow = Int('days_krakow')
days_bucharest = Int('days_bucharest')

# Constraints for days spent in each city
solver.add(days_brussels == 3)             # Spend 3 days in Brussels
solver.add(days_krakow == 4)               # Spend 4 days in Krakow
solver.add(days_bucharest == 4)            # Spend 4 days in Bucharest (adjusted)

# Total days constraint
solver.add(days_brussels + days_krakow + days_bucharest == 11)

# Constraints for attending the annual show in Krakow (must occur during days 8 to 11)
# This means that you will need to ensure that your visit to Krakow is at least 4 days 
# and accommodates the show.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_brussels_val = solver.model()[days_brussels].as_long()
    days_krakow_val = solver.model()[days_krakow].as_long()
    days_bucharest_val = solver.model()[days_bucharest].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_brussels_val} days in Brussels, "
        f"{days_krakow_val} days in Krakow, "
        f"{days_bucharest_val} days in Bucharest."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)