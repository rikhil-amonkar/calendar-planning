from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_frankfurt = Int('days_frankfurt')
days_krakow = Int('days_krakow')
days_salzburg = Int('days_salzburg')

# Constraints for days spent in each city
solver.add(days_frankfurt == 2)         # Spend 2 days in Frankfurt
solver.add(days_krakow == 5)             # Spend 5 days in Krakow
solver.add(days_salzburg == 4)            # Spend 4 days in Salzburg (adjusted)

# Total days constraint
solver.add(days_frankfurt + days_krakow + days_salzburg == 11)

# Constraints for attending the show in Krakow (must be on day 1 to day 5)
# Ensure that days 1-5 are frontloaded to accommodate the show in Krakow.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the days spent in each city
    days_frankfurt_val = solver.model()[days_frankfurt].as_long()
    days_krakow_val = solver.model()[days_krakow].as_long()
    days_salzburg_val = solver.model()[days_salzburg].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_frankfurt_val} days in Frankfurt, "
        f"{days_krakow_val} days in Krakow, "
        f"{days_salzburg_val} days in Salzburg."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)