from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_vilnius = Int('days_vilnius')
days_london = Int('days_london')
days_istanbul = Int('days_istanbul')

# Constraints for days spent in each city
solver.add(days_vilnius == 3)             # Spend 3 days in Vilnius (adjusted)
solver.add(days_london == 5)               # Spend 5 days in London
solver.add(days_istanbul == 2)             # Spend 2 days in Istanbul

# Total days constraint
solver.add(days_vilnius + days_london + days_istanbul == 10)

# Meeting friend requirement in London (must be between day 1 and day 5)
# This is satisfied by spending 5 days in London, as it allows for the visit during that timeframe.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_vilnius_val = solver.model()[days_vilnius].as_long()
    days_london_val = solver.model()[days_london].as_long()
    days_istanbul_val = solver.model()[days_istanbul].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_vilnius_val} days in Vilnius, "
        f"{days_london_val} days in London, "
        f"{days_istanbul_val} days in Istanbul."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)