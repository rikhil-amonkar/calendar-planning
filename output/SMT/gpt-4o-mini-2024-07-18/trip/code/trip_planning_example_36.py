from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_florence = Int('days_florence')
days_warsaw = Int('days_warsaw')
days_munich = Int('days_munich')

# Constraints for days spent in each city
solver.add(days_florence == 2)            # Spend 2 days in Florence
solver.add(days_warsaw == 7)              # Spend 7 days in Warsaw
solver.add(days_munich == 6)              # Spend 6 days in Munich

# Total days constraint
solver.add(days_florence + days_warsaw + days_munich == 13)

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_florence_val = solver.model()[days_florence].as_long()
    days_warsaw_val = solver.model()[days_warsaw].as_long()
    days_munich_val = solver.model()[days_munich].as_long()

    # Create a trip plan description
    valid_trip = (
        f"Spend {days_florence_val} days in Florence, "
        f"{days_warsaw_val} days in Warsaw, "
        f"{days_munich_val} days in Munich."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)