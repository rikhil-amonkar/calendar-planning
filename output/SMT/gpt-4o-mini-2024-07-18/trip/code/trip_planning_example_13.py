from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_lyon = Int('days_lyon')
days_bucharest = Int('days_bucharest')
days_manchester = Int('days_manchester')

# Constraints for days spent in each city
solver.add(days_lyon == 5)              # Spend 5 days in Lyon
solver.add(days_bucharest == 7)         # Spend 7 days in Bucharest
solver.add(days_manchester == 7)        # Spend 7 days in Manchester

# Total days constraint
solver.add(days_lyon + days_bucharest + days_manchester == 17)

# Constraints for visiting relatives in Lyon (must be on days 13 to 17)
# This means that you should surely allocate the last 5 days to Lyon.
# So we know that the days dedicated to Lyon will have to be overlapping
# with days 13 to 17.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_lyon_val = solver.model()[days_lyon].as_long()
    days_bucharest_val = solver.model()[days_bucharest].as_long()
    days_manchester_val = solver.model()[days_manchester].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_lyon_val} days in Lyon, "
        f"{days_bucharest_val} days in Bucharest, "
        f"{days_manchester_val} days in Manchester."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)