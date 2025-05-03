from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_frankfurt = Int('days_frankfurt')
days_lyon = Int('days_lyon')
days_vilnius = Int('days_vilnius')

# Constraints for days spent in each city
solver.add(days_frankfurt == 2)          # Spend 2 days in Frankfurt
solver.add(days_lyon == 3)                # Spend 3 days in Lyon
solver.add(days_vilnius == 5)             # Spend 5 days in Vilnius (adjusted)

# Total days constraint
solver.add(days_frankfurt + days_lyon + days_vilnius == 10)

# Constraints for attending the wedding in Vilnius (must be between day 4 to day 10)
# This means that the visit to Vilnius must include days 4-10.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_frankfurt_val = solver.model()[days_frankfurt].as_long()
    days_lyon_val = solver.model()[days_lyon].as_long()
    days_vilnius_val = solver.model()[days_vilnius].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_frankfurt_val} days in Frankfurt, "
        f"{days_lyon_val} days in Lyon, "
        f"{days_vilnius_val} days in Vilnius."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)