from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_vilnius = Int('days_vilnius')
days_munich = Int('days_munich')
days_mykonos = Int('days_mykonos')

# Constraints for days spent in each city
solver.add(days_vilnius == 4)            # Spend 4 days in Vilnius
solver.add(days_munich == 3)             # Spend 3 days in Munich
solver.add(days_mykonos == 5)            # Spend 5 days in Mykonos (adjusted)

# Total days constraint
solver.add(days_vilnius + days_munich + days_mykonos == 12)

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_vilnius_val = solver.model()[days_vilnius].as_long()
    days_munich_val = solver.model()[days_munich].as_long()
    days_mykonos_val = solver.model()[days_mykonos].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_vilnius_val} days in Vilnius, "
        f"{days_munich_val} days in Munich, "
        f"{days_mykonos_val} days in Mykonos."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)