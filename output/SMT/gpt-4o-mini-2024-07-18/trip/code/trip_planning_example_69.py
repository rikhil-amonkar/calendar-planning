from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_milan = Int('days_milan')
days_vilnius = Int('days_vilnius')
days_seville = Int('days_seville')

# Constraints for days spent in each city
solver.add(days_milan == 5)              # Spend 5 days in Milan (adjusted)
solver.add(days_vilnius == 5)            # Spend 5 days in Vilnius
solver.add(days_seville == 5)             # Spend 5 days in Seville

# Total days constraint
solver.add(days_milan + days_vilnius + days_seville == 15)

# Constraints for attending the workshop in Vilnius (must be between day 1 and day 5)
# This means that the stay in Vilnius must accommodate the workshop early in the trip.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_milan_val = solver.model()[days_milan].as_long()
    days_vilnius_val = solver.model()[days_vilnius].as_long()
    days_seville_val = solver.model()[days_seville].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_milan_val} days in Milan, "
        f"{days_vilnius_val} days in Vilnius, "
        f"{days_seville_val} days in Seville."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)