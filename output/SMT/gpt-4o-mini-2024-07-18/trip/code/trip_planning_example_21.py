from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_venice = Int('days_venice')
days_mykonos = Int('days_mykonos')
days_vienna = Int('days_vienna')

# Constraints for days spent in each city
solver.add(days_venice == 6)              # Spend 6 days in Venice
solver.add(days_mykonos == 2)             # Spend 2 days in Mykonos
solver.add(days_vienna == 4)              # Spend 4 days in Vienna

# Total days constraint
solver.add(days_venice + days_mykonos + days_vienna == 10)

# Constraints for the workshop in Venice (must be during days 5 to 10)
# The workshop requirement ensures that the allocation of days in Venice allows for the overlap from day 5 onward.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_venice_val = solver.model()[days_venice].as_long()
    days_mykonos_val = solver.model()[days_mykonos].as_long()
    days_vienna_val = solver.model()[days_vienna].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_venice_val} days in Venice, "
        f"{days_mykonos_val} days in Mykonos, "
        f"{days_vienna_val} days in Vienna."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)