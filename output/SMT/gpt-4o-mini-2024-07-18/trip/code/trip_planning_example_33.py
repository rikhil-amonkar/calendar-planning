from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_krakow = Int('days_krakow')
days_rome = Int('days_rome')
days_barcelona = Int('days_barcelona')

# Constraints for days spent in each city
solver.add(days_krakow == 4)           # Spend 4 days in Krakow
solver.add(days_rome == 4)             # Spend 4 days in Rome
solver.add(days_barcelona == 7)        # Spend 7 days in Barcelona

# Total days constraint
solver.add(days_krakow + days_rome + days_barcelona == 13)

# Constraints for meeting a friend in Krakow (must be between day 10 and day 13).
# This indicates that the visit to Krakow should be arranged such that you are 
# in the city on days 10, 11, 12, and 13. Therefore, you will need to be in Krakow 
# which overlaps with the last days of your trip.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_krakow_val = solver.model()[days_krakow].as_long()
    days_rome_val = solver.model()[days_rome].as_long()
    days_barcelona_val = solver.model()[days_barcelona].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_krakow_val} days in Krakow, "
        f"{days_rome_val} days in Rome, "
        f"{days_barcelona_val} days in Barcelona."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)