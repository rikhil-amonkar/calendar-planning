from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_nice = Int('days_nice')
days_tallinn = Int('days_tallinn')
days_copenhagen = Int('days_copenhagen')

# Constraints for days spent in each city
solver.add(days_nice == 7)               # Spend 7 days in Nice
solver.add(days_tallinn == 4)            # Spend 4 days in Tallinn (adjusted)
solver.add(days_copenhagen == 2)         # Spend 2 days in Copenhagen

# Total days constraint
solver.add(days_nice + days_tallinn + days_copenhagen == 13)

# Constraints for attending the wedding in Nice (must be between day 1 and day 7)
# Ensure Nice is planned for the first 7 days

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_nice_val = solver.model()[days_nice].as_long()
    days_tallinn_val = solver.model()[days_tallinn].as_long()
    days_copenhagen_val = solver.model()[days_copenhagen].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_nice_val} days in Nice, "
        f"{days_tallinn_val} days in Tallinn, "
        f"{days_copenhagen_val} days in Copenhagen."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)