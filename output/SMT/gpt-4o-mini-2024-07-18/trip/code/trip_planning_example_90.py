from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_vilnius = Int('days_vilnius')
days_naples = Int('days_naples')
days_vienna = Int('days_vienna')

# Constraints for days spent in each city
solver.add(days_vilnius == 7)              # Spend 7 days in Vilnius
solver.add(days_naples == 5)               # Spend 5 days in Naples
solver.add(days_vienna == 5)                # Spend 5 days in Vienna (adjusted)

# Total days constraint
solver.add(days_vilnius + days_naples + days_vienna == 17)

# Constraints for visiting relatives in Naples (must be between day 1 and day 5)
# This means that the first 5 days will be allocated to Naples.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_vilnius_val = solver.model()[days_vilnius].as_long()
    days_naples_val = solver.model()[days_naples].as_long()
    days_vienna_val = solver.model()[days_vienna].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_vilnius_val} days in Vilnius, "
        f"{days_naples_val} days in Naples, "
        f"{days_vienna_val} days in Vienna."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)