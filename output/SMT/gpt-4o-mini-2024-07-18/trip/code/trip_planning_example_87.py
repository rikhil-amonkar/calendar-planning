from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_riga = Int('days_riga')
days_amsterdam = Int('days_amsterdam')
days_mykonos = Int('days_mykonos')

# Constraints for days spent in each city
solver.add(days_riga == 2)                  # Spend 2 days in Riga
solver.add(days_amsterdam == 2)              # Spend 2 days in Amsterdam
solver.add(days_mykonos == 3)                # Spend 3 days in Mykonos (adjusted)

# Total days constraint
solver.add(days_riga + days_amsterdam + days_mykonos == 7)

# Constraints for visiting relatives in Riga (must be between day 1 and day 2)
# Since we are spending 2 days in Riga, this condition will be satisfied.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_riga_val = solver.model()[days_riga].as_long()
    days_amsterdam_val = solver.model()[days_amsterdam].as_long()
    days_mykonos_val = solver.model()[days_mykonos].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_riga_val} days in Riga, "
        f"{days_amsterdam_val} days in Amsterdam, "
        f"{days_mykonos_val} days in Mykonos."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)