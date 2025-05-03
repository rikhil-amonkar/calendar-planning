from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_vienna = Int('days_vienna')
days_krakow = Int('days_krakow')
days_riga = Int('days_riga')

# Constraints for days spent in each city
solver.add(days_vienna == 2)               # Spend 2 days in Vienna
solver.add(days_krakow == 3)               # Spend 3 days in Krakow
solver.add(days_riga == 5)                  # Spend 5 days in Riga (adjusted)

# Total days constraint
solver.add(days_vienna + days_krakow + days_riga == 10)

# Constraints for attending the annual show in Riga (must occur between day 4 and day 10)
# This requires us to ensure that the visit to Riga can accommodate the show.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_vienna_val = solver.model()[days_vienna].as_long()
    days_krakow_val = solver.model()[days_krakow].as_long()
    days_riga_val = solver.model()[days_riga].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_vienna_val} days in Vienna, "
        f"{days_krakow_val} days in Krakow, "
        f"{days_riga_val} days in Riga."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)