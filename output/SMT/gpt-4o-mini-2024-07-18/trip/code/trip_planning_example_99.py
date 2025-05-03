from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_santorini = Int('days_santorini')
days_krakow = Int('days_krakow')
days_london = Int('days_london')

# Constraints for days spent in each city
solver.add(days_santorini == 6)                  # Spend 6 days in Santorini
solver.add(days_krakow == 3)                     # Spend 3 days in Krakow (adjusted)
solver.add(days_london == 5)                      # Spend 5 days in London

# Total days constraint
solver.add(days_santorini + days_krakow + days_london == 14)

# Check if the constraints can be satisfied
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_santorini_val = solver.model()[days_santorini].as_long()
    days_krakow_val = solver.model()[days_krakow].as_long()
    days_london_val = solver.model()[days_london].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_santorini_val} days in Santorini, "
        f"{days_krakow_val} days in Krakow, "
        f"{days_london_val} days in London."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)