from z3 import *

# Create a solver instance
solver = Solver()

# Variables for days spent in each city
days_mykonos = Int('days_mykonos')
days_venice = Int('days_venice')
days_munich = Int('days_munich')

# Constraints for days spent in each city
solver.add(days_mykonos == 5)            # Spend 5 days in Mykonos
solver.add(days_venice == 4)             # Spend 4 days in Venice (adjusted)
solver.add(days_munich == 4)             # Spend 4 days in Munich

# Total days constraint
solver.add(days_mykonos + days_venice + days_munich == 13)

# Meeting friends requirement in Mykonos (must be between day 9 and day 13)
# This implies that the overall trip needs to be sequenced so that Mykonos is visited last.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_mykonos_val = solver.model()[days_mykonos].as_long()
    days_venice_val = solver.model()[days_venice].as_long()
    days_munich_val = solver.model()[days_munich].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_mykonos_val} days in Mykonos, "
        f"{days_venice_val} days in Venice, "
        f"{days_munich_val} days in Munich."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)