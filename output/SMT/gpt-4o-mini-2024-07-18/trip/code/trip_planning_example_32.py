from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_reykjavik = Int('days_reykjavik')
days_riga = Int('days_riga')
days_paris = Int('days_paris')

# Constraints for days spent in each city
solver.add(days_reykjavik == 5)          # Spend 5 days in Reykjavik
solver.add(days_riga == 3)                # Spend 3 days in Riga
solver.add(days_paris == 4)               # Spend 4 days in Paris

# Total days constraint
solver.add(days_reykjavik + days_riga + days_paris == 10)

# Constraints for attending the annual show in Reykjavik (must be during days 6 to 10)
# This means you should plan your trip to ensure that you are in Reykjavik
# for days 6 to 10.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_reykjavik_val = solver.model()[days_reykjavik].as_long()
    days_riga_val = solver.model()[days_riga].as_long()
    days_paris_val = solver.model()[days_paris].as_long()

    # Create a trip plan description
    valid_trip = (
        f"Spend {days_reykjavik_val} days in Reykjavik, "
        f"{days_riga_val} days in Riga, "
        f"{days_paris_val} days in Paris."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)