from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_vienna = Int('days_vienna')
days_vilnius = Int('days_vilnius')
days_valencia = Int('days_valencia')

# Constraints for days spent in each city
solver.add(days_vienna == 5)            # Spend 5 days in Vienna
solver.add(days_vilnius == 5)           # Spend 5 days in Vilnius
solver.add(days_valencia == 7)          # Spend 7 days in Valencia

# Total days constraint
solver.add(days_vienna + days_vilnius + days_valencia == 15)

# Constraints for the conferences in Valencia
# On day 9 and day 15 you need to be in Valencia.
# Hence, you must visit Valencia with enough days to cover these requirements.
# As you have 7 days in Valencia, this can be planned to ensure coverage.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_vienna_val = solver.model()[days_vienna].as_long()
    days_vilnius_val = solver.model()[days_vilnius].as_long()
    days_valencia_val = solver.model()[days_valencia].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_vienna_val} days in Vienna, "
        f"{days_vilnius_val} days in Vilnius, "
        f"{days_valencia_val} days in Valencia."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)