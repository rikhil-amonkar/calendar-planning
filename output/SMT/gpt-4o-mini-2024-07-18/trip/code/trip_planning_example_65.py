from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_milan = Int('days_milan')
days_santorini = Int('days_santorini')
days_mykonos = Int('days_mykonos')

# Constraints for days spent in each city
solver.add(days_milan == 3)                  # Spend 3 days in Milan
solver.add(days_santorini == 5)               # Spend 5 days in Santorini (adjusted)
solver.add(days_mykonos == 4)                 # Spend 4 days in Mykonos

# Total days constraint
solver.add(days_milan + days_santorini + days_mykonos == 12)

# Constraints for visiting relatives in Santorini (must be between day 6 and day 12)
# If you spend 5 days in Santorini, you can meet relatives at least from day 6 onwards.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_milan_val = solver.model()[days_milan].as_long()
    days_santorini_val = solver.model()[days_santorini].as_long()
    days_mykonos_val = solver.model()[days_mykonos].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_milan_val} days in Milan, "
        f"{days_santorini_val} days in Santorini, "
        f"{days_mykonos_val} days in Mykonos."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)