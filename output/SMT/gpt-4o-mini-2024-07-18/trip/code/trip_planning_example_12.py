from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_valencia = Int('days_valencia')
days_amsterdam = Int('days_amsterdam')
days_tallinn = Int('days_tallinn')

# Constraints for days spent in each city
solver.add(days_valencia == 5)            # Spend 5 days in Valencia
solver.add(days_amsterdam == 5)           # Spend 5 days in Amsterdam
solver.add(days_tallinn == 7)             # Spend 7 days in Tallinn

# Total days constraint
solver.add(days_valencia + days_amsterdam + days_tallinn == 15)

# Meeting constraint in Tallinn (between days 9 and 15)
# Since you spend 7 days in Tallinn and must meet your friend,
# You should be able to occupy days 9 to 15 within those visits.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_valencia_val = solver.model()[days_valencia].as_long()
    days_amsterdam_val = solver.model()[days_amsterdam].as_long()
    days_tallinn_val = solver.model()[days_tallinn].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_valencia_val} days in Valencia, "
        f"{days_amsterdam_val} days in Amsterdam, "
        f"{days_tallinn_val} days in Tallinn."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)