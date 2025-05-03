from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_frankfurt = Int('days_frankfurt')
days_bucharest = Int('days_bucharest')
days_berlin = Int('days_berlin')

# Constraints for days spent in each city
solver.add(days_frankfurt == 4)          # Spend 4 days in Frankfurt
solver.add(days_bucharest == 2)           # Spend 2 days in Bucharest
solver.add(days_berlin == 7)              # Spend 7 days in Berlin

# Total days constraint
solver.add(days_frankfurt + days_bucharest + days_berlin == 11)

# Constraints for the annual show in Berlin (must be attended from day 1 to day 7)
# Since part of Berlin days overlaps with days 1 to 7; this meets the requirement.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_frankfurt_val = solver.model()[days_frankfurt].as_long()
    days_bucharest_val = solver.model()[days_bucharest].as_long()
    days_berlin_val = solver.model()[days_berlin].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_frankfurt_val} days in Frankfurt, "
        f"{days_bucharest_val} days in Bucharest, "
        f"{days_berlin_val} days in Berlin."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)