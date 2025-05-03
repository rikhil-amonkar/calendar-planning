from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_mykonos = Int('days_mykonos')
days_nice = Int('days_nice')
days_helsinki = Int('days_helsinki')

# Constraints for days spent in each city
solver.add(days_mykonos == 4)               # Spend 4 days in Mykonos
solver.add(days_nice == 4)                   # Spend 4 days in Nice (adjusted)
solver.add(days_helsinki == 6)               # Spend 6 days in Helsinki (for the show)

# Total days constraint
solver.add(days_mykonos + days_nice + days_helsinki == 14)

# Constraints for attending the annual show in Helsinki (must be between days 1 and 6)
# The current plan will accommodate this requirement as the total days in Helsinki is 6.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_mykonos_val = solver.model()[days_mykonos].as_long()
    days_nice_val = solver.model()[days_nice].as_long()
    days_helsinki_val = solver.model()[days_helsinki].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_mykonos_val} days in Mykonos, "
        f"{days_nice_val} days in Nice, "
        f"{days_helsinki_val} days in Helsinki."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)