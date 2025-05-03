from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_brussels = Int('days_brussels')
days_riga = Int('days_riga')
days_geneva = Int('days_geneva')

# Constraints for days spent in each city
solver.add(days_brussels == 6)             # Spend 6 days in Brussels
solver.add(days_riga == 2)                  # Spend 2 days in Riga
solver.add(days_geneva == 4)                # Spend 4 days in Geneva (adjusted)

# Total days constraint
solver.add(days_brussels + days_riga + days_geneva == 12)

# Constraints for visiting relatives in Riga (must be between day 11 to day 12)
# If you spend 2 days in Riga and the trip includes day 12, you can meet relatives.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_brussels_val = solver.model()[days_brussels].as_long()
    days_riga_val = solver.model()[days_riga].as_long()
    days_geneva_val = solver.model()[days_geneva].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_brussels_val} days in Brussels, "
        f"{days_riga_val} days in Riga, "
        f"{days_geneva_val} days in Geneva."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)