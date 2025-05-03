from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_brussels = Int('days_brussels')
days_valencia = Int('days_valencia')
days_nice = Int('days_nice')

# Constraints for days spent in each city
solver.add(days_brussels == 2)           # Spend 2 days in Brussels
solver.add(days_valencia == 3)           # Spend 3 days in Valencia
solver.add(days_nice == 6)               # Spend 6 days in Nice

# Total days constraint
solver.add(days_brussels + days_valencia + days_nice == 9)

# Constraints for meeting friends in Nice (must occur between day 1 and day 6)
# You need to arrive in Nice on or before day 6, 
# and given that you're spending 6 days, you can arrange your schedule to fit.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_brussels_val = solver.model()[days_brussels].as_long()
    days_valencia_val = solver.model()[days_valencia].as_long()
    days_nice_val = solver.model()[days_nice].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_brussels_val} days in Brussels, "
        f"{days_valencia_val} days in Valencia, "
        f"{days_nice_val} days in Nice."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)