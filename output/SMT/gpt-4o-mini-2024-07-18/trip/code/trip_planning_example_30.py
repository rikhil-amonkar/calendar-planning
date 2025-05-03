from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_istanbul = Int('days_istanbul')
days_tallinn = Int('days_tallinn')
days_zurich = Int('days_zurich')

# Constraints for days spent in each city
solver.add(days_istanbul == 5)          # Spend 5 days in Istanbul
solver.add(days_tallinn == 4)           # Spend 4 days in Tallinn
solver.add(days_zurich == 7)            # Spend 7 days in Zurich

# Total days constraint
solver.add(days_istanbul + days_tallinn + days_zurich == 14)

# Constraints for attending the annual show in Zurich (must be attended from day 1 to 7)
# Therefore, the stay in Zurich must cover the first 7 days of the trip.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_istanbul_val = solver.model()[days_istanbul].as_long()
    days_tallinn_val = solver.model()[days_tallinn].as_long()
    days_zurich_val = solver.model()[days_zurich].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_istanbul_val} days in Istanbul, "
        f"{days_tallinn_val} days in Tallinn, "
        f"{days_zurich_val} days in Zurich."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)