from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_krakow = Int('days_krakow')
days_dubrovnik = Int('days_dubrovnik')
days_frankfurt = Int('days_frankfurt')

# Constraints for days spent in each city
solver.add(days_krakow == 2)              # Spend 2 days in Krakow
solver.add(days_dubrovnik == 7)           # Spend 7 days in Dubrovnik
solver.add(days_frankfurt == 3)           # Spend 3 days in Frankfurt

# Total days constraint
solver.add(days_krakow + days_dubrovnik + days_frankfurt == 10)

# Constraints for attending the wedding in Krakow (must be on days 9 or 10)
# You must arrive in Krakow so that you're there for the wedding on day 9 or 10.
# This implies you can only stay in Krakow in the last two days of your stay.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_krakow_val = solver.model()[days_krakow].as_long()
    days_dubrovnik_val = solver.model()[days_dubrovnik].as_long()
    days_frankfurt_val = solver.model()[days_frankfurt].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_krakow_val} days in Krakow, "
        f"{days_dubrovnik_val} days in Dubrovnik, "
        f"{days_frankfurt_val} days in Frankfurt."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)