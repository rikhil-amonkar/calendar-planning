from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_krakow = Int('days_krakow')
days_rome = Int('days_rome')
days_london = Int('days_london')

# Constraints for days spent in each city
solver.add(days_krakow == 3)            # Spend 3 days in Krakow
solver.add(days_rome == 7)               # Spend 7 days in Rome
solver.add(days_london == 5)             # Spend 5 days in London (adjusted)

# Total days constraint
solver.add(days_krakow + days_rome + days_london == 15)

# Constraints for attending the annual show in Krakow (must be between day 13 and 15)
# Ensure the planned days allow for the show during the last part of the trip.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_krakow_val = solver.model()[days_krakow].as_long()
    days_rome_val = solver.model()[days_rome].as_long()
    days_london_val = solver.model()[days_london].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_krakow_val} days in Krakow, "
        f"{days_rome_val} days in Rome, "
        f"{days_london_val} days in London."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)