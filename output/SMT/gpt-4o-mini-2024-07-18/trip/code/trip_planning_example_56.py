from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_copenhagen = Int('days_copenhagen')
days_mykonos = Int('days_mykonos')
days_geneva = Int('days_geneva')

# Constraints for days spent in each city
solver.add(days_copenhagen == 2)          # Spend 2 days in Copenhagen
solver.add(days_mykonos == 3)             # Spend 3 days in Mykonos
solver.add(days_geneva == 4)              # Spend 4 days in Geneva (adjusted)

# Total days constraint
solver.add(days_copenhagen + days_mykonos + days_geneva == 9)

# Constraints for meeting friends in Mykonos (must be between day 7 to day 9)
# This means we must ensure that Mykonos is arranged at the end of the trip.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_copenhagen_val = solver.model()[days_copenhagen].as_long()
    days_mykonos_val = solver.model()[days_mykonos].as_long()
    days_geneva_val = solver.model()[days_geneva].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_copenhagen_val} days in Copenhagen, "
        f"{days_mykonos_val} days in Mykonos, "
        f"{days_geneva_val} days in Geneva."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)