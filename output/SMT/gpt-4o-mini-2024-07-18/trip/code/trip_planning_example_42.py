from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_paris = Int('days_paris')
days_mykonos = Int('days_mykonos')
days_nice = Int('days_nice')

# Constraints for days spent in each city
solver.add(days_paris == 4)               # Spend 4 days in Paris
solver.add(days_mykonos == 4)             # Spend 4 days in Mykonos
solver.add(days_nice == 5)                # Spend 5 days in Nice

# Total days constraint
solver.add(days_paris + days_mykonos + days_nice == 11)

# Constraint for meeting friends in Paris (must be between day 1 to day 4)
# This means that the stay in Paris must overlap with the first four days.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_paris_val = solver.model()[days_paris].as_long()
    days_mykonos_val = solver.model()[days_mykonos].as_long()
    days_nice_val = solver.model()[days_nice].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_paris_val} days in Paris, "
        f"{days_mykonos_val} days in Mykonos, "
        f"{days_nice_val} days in Nice."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)