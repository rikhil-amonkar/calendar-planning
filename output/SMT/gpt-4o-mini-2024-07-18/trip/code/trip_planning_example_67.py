from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_manchester = Int('days_manchester')
days_split = Int('days_split')
days_dublin = Int('days_dublin')

# Constraints for days spent in each city
solver.add(days_manchester == 3)           # Spend 3 days in Manchester
solver.add(days_split == 7)                 # Spend 7 days in Split
solver.add(days_dublin == 3)                 # Spend 3 days in Dublin (adjusted)

# Total days constraint
solver.add(days_manchester + days_split + days_dublin == 13)

# Constraints for visiting relatives in Manchester (must be between day 5 to day 7)
# We need to ensure that Manchester is planned such that it accommodates the relative visit
# After spending 3 days in Manchester, you'll need to visit before leaving for Split.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_manchester_val = solver.model()[days_manchester].as_long()
    days_split_val = solver.model()[days_split].as_long()
    days_dublin_val = solver.model()[days_dublin].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_manchester_val} days in Manchester, "
        f"{days_split_val} days in Split, "
        f"{days_dublin_val} days in Dublin."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)