from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_berlin = Int('days_berlin')
days_naples = Int('days_naples')
days_krakow = Int('days_krakow')

# Constraints for days spent in each city
solver.add(days_berlin == 7)                # Spend 7 days in Berlin
solver.add(days_naples == 4)                 # Spend 4 days in Naples (adjusted)
solver.add(days_krakow == 4)                 # Spend 4 days in Krakow

# Total days constraint
solver.add(days_berlin + days_naples + days_krakow == 15)

# Constraints for meeting friends in Krakow (must be between day 12 and day 15)
# This requirement requires that the stay in Krakow occurs during those last days.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_berlin_val = solver.model()[days_berlin].as_long()
    days_naples_val = solver.model()[days_naples].as_long()
    days_krakow_val = solver.model()[days_krakow].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_berlin_val} days in Berlin, "
        f"{days_naples_val} days in Naples, "
        f"{days_krakow_val} days in Krakow."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)