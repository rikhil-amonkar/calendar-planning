from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_berlin = Int('days_berlin')
days_porto = Int('days_porto')
days_krakow = Int('days_krakow')

# Constraints for days spent in each city
solver.add(days_berlin == 6)             # Spend 6 days in Berlin
solver.add(days_porto == 2)               # Spend 2 days in Porto
solver.add(days_krakow == 5)              # Spend 5 days in Krakow

# Total days constraint
solver.add(days_berlin + days_porto + days_krakow == 11)

# Constraints for the wedding in Porto (must be on days 10 and 11)
# To attend the wedding, you need to be in Porto for days 10 and 11.
# Therefore, this indicates that you'll need to be in Porto on those last two days,
# which will be the 2 days you are allocating to Porto.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_berlin_val = solver.model()[days_berlin].as_long()
    days_porto_val = solver.model()[days_porto].as_long()
    days_krakow_val = solver.model()[days_krakow].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_berlin_val} days in Berlin, "
        f"{days_porto_val} days in Porto, "
        f"{days_krakow_val} days in Krakow."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)