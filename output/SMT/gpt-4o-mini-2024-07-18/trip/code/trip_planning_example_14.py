from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_lyon = Int('days_lyon')
days_krakow = Int('days_krakow')
days_frankfurt = Int('days_frankfurt')

# Constraints for days spent in each city
solver.add(days_lyon == 7)              # Spend 7 days in Lyon
solver.add(days_krakow == 3)            # Spend 3 days in Krakow
solver.add(days_frankfurt == 2)         # Spend 2 days in Frankfurt

# Total days constraint
solver.add(days_lyon + days_krakow + days_frankfurt == 10)

# Constraints for the show in Krakow (must be during days 8 to 10)
# This means you need to arrive in Krakow before day 8 to attend the annual show,
# so Krakow must be visited after spending days in Lyon and Frankfurt. 

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_lyon_val = solver.model()[days_lyon].as_long()
    days_krakow_val = solver.model()[days_krakow].as_long()
    days_frankfurt_val = solver.model()[days_frankfurt].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_lyon_val} days in Lyon, "
        f"{days_frankfurt_val} days in Frankfurt, "
        f"{days_krakow_val} days in Krakow."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)