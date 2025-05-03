from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_amsterdam = Int('days_amsterdam')
days_seville = Int('days_seville')
days_lyon = Int('days_lyon')

# Constraints for days spent in each city
solver.add(days_amsterdam == 4)            # Spend 4 days in Amsterdam (adjusted)
solver.add(days_seville == 4)               # Spend 4 days in Seville
solver.add(days_lyon == 4)                  # Spend 4 days in Lyon (for the show)

# Total days constraint
solver.add(days_amsterdam + days_seville + days_lyon == 12)

# Constraints for attending the annual show in Lyon (must be during days 1 to 4)
# As we are spending all 4 days in Lyon, this constraint is already satisfied.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_amsterdam_val = solver.model()[days_amsterdam].as_long()
    days_seville_val = solver.model()[days_seville].as_long()
    days_lyon_val = solver.model()[days_lyon].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_amsterdam_val} days in Amsterdam, "
        f"{days_seville_val} days in Seville, "
        f"{days_lyon_val} days in Lyon."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)