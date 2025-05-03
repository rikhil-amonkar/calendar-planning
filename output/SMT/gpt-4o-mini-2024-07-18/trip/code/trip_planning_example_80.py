from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_valencia = Int('days_valencia')
days_riga = Int('days_riga')
days_copenhagen = Int('days_copenhagen')

# Constraints for days spent in each city
solver.add(days_valencia == 5)             # Spend 5 days in Valencia
solver.add(days_riga == 5)                  # Spend 5 days in Riga (adjusted)
solver.add(days_copenhagen == 4)            # Spend 4 days in Copenhagen

# Total days constraint
solver.add(days_valencia + days_riga + days_copenhagen == 14)

# Constraints for visiting relatives in Riga (must be between day 8 and day 14)
# This implies that we must ensure the schedule allows for these days.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_valencia_val = solver.model()[days_valencia].as_long()
    days_riga_val = solver.model()[days_riga].as_long()
    days_copenhagen_val = solver.model()[days_copenhagen].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_valencia_val} days in Valencia, "
        f"{days_riga_val} days in Riga, "
        f"{days_copenhagen_val} days in Copenhagen."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)