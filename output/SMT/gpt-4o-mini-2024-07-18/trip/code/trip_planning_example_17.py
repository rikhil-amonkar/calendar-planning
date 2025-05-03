from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_copenhagen = Int('days_copenhagen')
days_vienna = Int('days_vienna')
days_lyon = Int('days_lyon')

# Constraints for days spent in each city
solver.add(days_copenhagen == 5)              # Spend 5 days in Copenhagen
solver.add(days_vienna == 4)                  # Spend 4 days in Vienna
solver.add(days_lyon == 4)                    # Spend 4 days in Lyon

# Total days constraint
solver.add(days_copenhagen + days_vienna + days_lyon == 11)

# Constraints for attending the conference in Copenhagen
# You must be in Copenhagen on days 1 and 5.
# Since you're spending 5 days there, you can occupy days 1-5.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_copenhagen_val = solver.model()[days_copenhagen].as_long()
    days_vienna_val = solver.model()[days_vienna].as_long()
    days_lyon_val = solver.model()[days_lyon].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_copenhagen_val} days in Copenhagen, "
        f"{days_vienna_val} days in Vienna, "
        f"{days_lyon_val} days in Lyon."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)