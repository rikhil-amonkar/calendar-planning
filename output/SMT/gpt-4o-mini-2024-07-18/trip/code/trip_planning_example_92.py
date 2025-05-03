from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_riga = Int('days_riga')
days_vilnius = Int('days_vilnius')
days_dublin = Int('days_dublin')

# Constraints for days spent in each city
solver.add(days_riga == 5)                  # Spend 5 days in Riga
solver.add(days_vilnius == 5)                # Spend 5 days in Vilnius (adjusted)
solver.add(days_dublin == 2)                 # Spend 2 days in Dublin

# Total days constraint
solver.add(days_riga + days_vilnius + days_dublin == 12)

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_riga_val = solver.model()[days_riga].as_long()
    days_vilnius_val = solver.model()[days_vilnius].as_long()
    days_dublin_val = solver.model()[days_dublin].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_riga_val} days in Riga, "
        f"{days_vilnius_val} days in Vilnius, "
        f"{days_dublin_val} days in Dublin."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)