from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_london = Int('days_london')
days_bucharest = Int('days_bucharest')
days_riga = Int('days_riga')

# Constraints for days spent in each city
solver.add(days_london == 3)            # Spend 3 days in London
solver.add(days_bucharest == 3)         # Spend 3 days in Bucharest
solver.add(days_riga == 4)              # Spend 4 days in Riga

# Total days constraint
solver.add(days_london + days_bucharest + days_riga == 8)

# Constraint for attending the workshop in Riga (must be between day 5 and day 8)
# Given that you spend 4 days in Riga, you need to ensure Riga is visited by day 5 –
# implying during the days valid to meet workshop attendance.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_london_val = solver.model()[days_london].as_long()
    days_bucharest_val = solver.model()[days_bucharest].as_long()
    days_riga_val = solver.model()[days_riga].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_london_val} days in London, "
        f"{days_bucharest_val} days in Bucharest, "
        f"{days_riga_val} days in Riga."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)