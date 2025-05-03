from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_amsterdam = Int('days_amsterdam')
days_vilnius = Int('days_vilnius')
days_bucharest = Int('days_bucharest')

# Constraints for days spent in each city
solver.add(days_amsterdam == 5)            # Spend 5 days in Amsterdam
solver.add(days_vilnius == 2)              # Spend 2 days in Vilnius
solver.add(days_bucharest == 6)            # Spend 6 days in Bucharest

# Total days constraint
solver.add(days_amsterdam + days_vilnius + days_bucharest == 11)

# Constraints for meeting friends in Bucharest (must be between day 6 and 11)
# Since Bucharest is being visited for 6 days, you need to ensure 
# that you arrive there before day 6 to be there for your friends.
# Thus, you can set the trip such that you ensure the overlap on days 
# 6 to 11.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_amsterdam_val = solver.model()[days_amsterdam].as_long()
    days_vilnius_val = solver.model()[days_vilnius].as_long()
    days_bucharest_val = solver.model()[days_bucharest].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_amsterdam_val} days in Amsterdam, "
        f"{days_vilnius_val} days in Vilnius, "
        f"{days_bucharest_val} days in Bucharest."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)